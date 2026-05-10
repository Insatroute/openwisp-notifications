import logging
from urllib.parse import quote

from allauth.account.models import EmailAddress
from celery.exceptions import OperationalError
from django.conf import settings
from django.contrib import messages
from django.contrib.auth import get_user_model
from django.contrib.auth.signals import user_logged_in
from django.contrib.contenttypes.models import ContentType
from django.core.cache import cache
from django.db import transaction
from django.db.models import Q
from django.db.models.query import QuerySet
from django.db.models.signals import post_delete, post_save, pre_save
from django.dispatch import receiver
from django.urls import reverse
from django.utils import timezone
from django.utils.html import format_html
from django.utils.translation import gettext as _

from openwisp_notifications import settings as app_settings
from openwisp_notifications import tasks
from openwisp_notifications.exceptions import NotificationRenderException
from openwisp_notifications.swapper import load_model, swapper_load_model
from openwisp_notifications.types import (
    NOTIFICATION_ASSOCIATED_MODELS,
    get_notification_configuration,
)
from openwisp_notifications.utils import get_user_email_preference
from openwisp_notifications.websockets import handlers as ws_handlers

logger = logging.getLogger(__name__)

EXTRA_DATA = app_settings.get_config()["USE_JSONFIELD"]

User = get_user_model()

Notification = load_model("Notification")
NotificationSetting = load_model("NotificationSetting")
IgnoreObjectNotification = load_model("IgnoreObjectNotification")

Group = swapper_load_model("openwisp_users", "Group")
OrganizationUser = swapper_load_model("openwisp_users", "OrganizationUser")
Organization = swapper_load_model("openwisp_users", "Organization")


def _get_alert_config(notification):
    """Get AlertConfiguration for this notification. Returns object or None."""
    try:
        target = None
        if notification.target_content_type and notification.target_object_id:
            target = notification.target_content_type.get_object_for_this_type(
                pk=notification.target_object_id
            )
        if target is None:
            return None
        org_id = getattr(target, "organization_id", None)
        if not org_id or not notification.type:
            return None
        from email_templates.models import AlertConfiguration
        return AlertConfiguration.objects.filter(
            organization_id=org_id,
            notification_type=notification.type,
            is_enabled=True,
        ).select_related('email_template').first()
    except Exception:
        return None


def _get_alert_email_timing(notification):
    ac = _get_alert_config(notification)
    return ac.email_timing if ac else None


def _send_custom_template_email(notification, alert_config):
    """Send email using custom EmailTemplate from AlertConfiguration."""
    template = alert_config.email_template
    if not template or not template.is_active:
        return False

    target = None
    try:
        if notification.target_content_type and notification.target_object_id:
            target = notification.target_content_type.get_object_for_this_type(
                pk=notification.target_object_id
            )
    except Exception:
        pass

    from django.contrib.sites.models import Site
    site = Site.objects.get_current()
    device_name = str(target) if target else "Unknown"
    # Some senders pass extras under a nested "data" kwarg (notify_handler keeps
    # that wrapping); others pass them as flat kwargs. Merge both shapes so the
    # downstream lookups (current_value, ifname, ...) work either way.
    _raw = notification.data or {}
    if isinstance(_raw.get('data'), dict):
        notif_data = {**_raw.get('data', {}), **{k: v for k, v in _raw.items() if k != 'data'}}
    else:
        notif_data = _raw

    org_name = ""
    if target:
        org = getattr(target, "organization", None)
        org_name = str(org) if org else ""

    device_url = f"https://{site.domain}/admin/"
    if target:
        try:
            ct = notification.target_content_type
            device_url = "https://{domain}{path}".format(
                domain=site.domain,
                path=reverse('admin:%s_%s_change' % (ct.app_label, ct.model), args=[target.pk])
            )
        except Exception:
            pass

    alert_type_map = dict(alert_config.NOTIFICATION_TYPE_CHOICES)
    alert_type = alert_type_map.get(notification.type, notification.type or '')

    ts = ""
    if notification.timestamp:
        ts = timezone.localtime(notification.timestamp).strftime("%B %d, %Y, %I:%M %p %Z")

    # threshold-vars-added: pull threshold (from AC.custom_threshold or
    # default 90 if unset), current observed value (from data dict, set by
    # the notifier), and computed problem-duration for recovery alerts.
    _threshold = alert_config.custom_threshold
    _threshold_str = (
        f"{_threshold:g}%" if _threshold is not None else ""
    )
    _current = notif_data.get('current_value')
    if _current is None:
        _current_str = ""
    else:
        try:
            _current_str = f"{float(_current):.2f}%"
        except (TypeError, ValueError):
            _current_str = str(_current)

    # For *_recovery, compute time spent in problem state by looking up
    # the matching *_problem notification that preceded this one.
    _problem_duration_str = ""
    if (notification.type or '').endswith('_recovery'):
        try:
            from openwisp_notifications.models import Notification as _N
            problem_type = (notification.type or '').replace('_recovery', '_problem')
            target_pk = str(target.pk) if target else None
            if target_pk:
                last_problem = (
                    _N.objects.filter(
                        target_object_id=target_pk,
                        type=problem_type,
                        timestamp__lt=notification.timestamp,
                    ).order_by("-timestamp").first()
                )
                if last_problem:
                    delta = notification.timestamp - last_problem.timestamp
                    total = int(delta.total_seconds())
                    h, rem = divmod(total, 3600)
                    m, s = divmod(rem, 60)
                    if h:
                        _problem_duration_str = f"{h}h {m}m"
                    elif m:
                        _problem_duration_str = f"{m}m {s}s"
                    else:
                        _problem_duration_str = f"{s}s"
        except Exception:
            pass

    # Per-type rendering: ping (and other binary/non-threshold alerts) don't
    # have a numeric threshold or observed value. Hide those rows and render a
    # status line that includes the duration since the issue began.
    ntype = notification.type or ''
    is_threshold_metric = bool(_threshold_str) and ntype in (
        'cpu_problem', 'cpu_recovery',
        'memory_problem', 'memory_recovery',
        'disk_problem', 'disk_recovery',
        'wifi_clients_max_problem', 'wifi_clients_max_recovery',
        'wifi_clients_min_problem', 'wifi_clients_min_recovery',
    )

    is_problem = ntype.endswith('_problem') or ntype in (
        'connection_is_not_working', 'interface_is_down', 'wan_internet_down',
        'tunnel_down', 'config_error', 'sla_violation', 'ha_split_brain',
    )

    # For binary problem alerts, compute "since X" using the last opposite-state
    # notification (mirror of how problem_duration is computed for recoveries).
    _since_str = ''
    if is_problem and not is_threshold_metric:
        try:
            from openwisp_notifications.models import Notification as _N
            recovery_pairs = {
                'ping_problem': 'ping_recovery',
                'connection_is_not_working': 'connection_is_working',
                'interface_is_down': 'interface_is_up',
                'wan_internet_down': 'wan_internet_up',
                'tunnel_down': 'tunnel_up',
                'data_collected_problem': 'data_collected_recovery',
            }
            opposite = recovery_pairs.get(ntype)
            target_pk = str(target.pk) if target else None
            if opposite and target_pk:
                last_ok = (
                    _N.objects.filter(
                        target_object_id=target_pk,
                        type=opposite,
                        timestamp__lt=notification.timestamp,
                    ).order_by('-timestamp').first()
                )
                if last_ok:
                    delta = notification.timestamp - last_ok.timestamp
                    total = int(delta.total_seconds())
                    h, rem = divmod(total, 3600)
                    m, s = divmod(rem, 60)
                    if h:
                        _since_str = f"{h}h {m}m"
                    elif m:
                        _since_str = f"{m}m {s}s"
                    else:
                        _since_str = f"{s}s"
        except Exception:
            pass

    # Build the conditional rows + status text.
    if is_threshold_metric:
        _threshold_row = (
            '<tr>'
            '<td style="padding:6px 0;color:#92400e;font-weight:600;width:42%;">Threshold (target)</td>'
            f'<td style="padding:6px 0;color:#1e293b;font-weight:700;">{_threshold_str}</td>'
            '</tr>'
        ) if ntype.endswith('_problem') else (
            '<tr>'
            '<td style="padding:6px 0;color:#15803d;font-weight:600;width:42%;">Threshold (target)</td>'
            f'<td style="padding:6px 0;color:#1e293b;font-weight:700;">{_threshold_str}</td>'
            '</tr>'
        )
        _current_row = (
            '<tr>'
            '<td style="padding:6px 0;color:#92400e;font-weight:600;">Current value (observed)</td>'
            f'<td style="padding:6px 0;color:#dc2626;font-weight:700;font-size:16px;">{_current_str}</td>'
            '</tr>'
        ) if ntype.endswith('_problem') else (
            '<tr>'
            '<td style="padding:6px 0;color:#15803d;font-weight:600;">Current value (observed)</td>'
            f'<td style="padding:6px 0;color:#16a34a;font-weight:700;font-size:16px;">{_current_str}</td>'
            '</tr>'
        )
        if ntype.endswith('_problem'):
            _status_text = (
                f"{alert_type} exceeded threshold ({_threshold_str} &lt; {_current_str})"
            )
        else:
            _status_text = (
                f"{alert_type} ({_current_str} &le; {_threshold_str})"
            )
    else:
        _threshold_row = ''
        _current_row = ''
        ifname = notif_data.get('ifname', '')
        # Interface / WAN events: prefix with the interface name so the row
        # reads e.g. "eth2 is down (since 5m 3s)".
        iface_phrasing = {
            'interface_is_down': ('{} is down', 'is down'),
            'interface_is_up': ('{} is up', 'is up'),
            'wan_internet_down': ('{} WAN internet is down', 'WAN internet down'),
            'wan_internet_up': ('{} WAN internet is up', 'WAN internet up'),
        }
        if ntype in iface_phrasing and ifname:
            phrase = iface_phrasing[ntype][0].format(ifname)
            if is_problem:
                _status_text = (
                    f"{phrase} (since {_since_str})" if _since_str else phrase
                )
            else:
                _status_text = (
                    f"{phrase} (was down for {_problem_duration_str})"
                    if _problem_duration_str else phrase
                )
        elif ntype == 'ping_problem':
            _status_text = (
                f"{device_name} facing {alert_type} for {_since_str}"
                if _since_str else f"{device_name} facing {alert_type}"
            )
        elif ntype == 'ping_recovery':
            _status_text = (
                f"{device_name} {alert_type} after {_problem_duration_str} in problem state"
                if _problem_duration_str else f"{device_name} {alert_type}"
            )
        elif is_problem:
            _status_text = (
                f"{alert_type} (since {_since_str})" if _since_str else alert_type
            )
        else:
            _status_text = (
                f"{alert_type} (was {_problem_duration_str})"
                if _problem_duration_str else alert_type
            )

    variables = {
        '{{ device_name }}': device_name,
        '{{ organization }}': org_name,
        '{{ site_name }}': site.name,
        '{{ site_domain }}': site.domain,
        '{{ notification_type }}': notification.type or '',
        '{{ alert_type }}': alert_type,
        '{{ level }}': notification.level or '',
        '{{ message }}': str(notification.message or ''),
        '{{ timestamp }}': ts,
        '{{ device_url }}': device_url,
        '{{ check_interval }}': str(alert_config.check_interval),
        '{{ retry_count }}': str(alert_config.retry_count),
        '{{ alert_after }}': str(alert_config.alert_after_minutes),
        '{{ interface_name }}': notif_data.get('ifname', ''),
        '{{ threshold }}': _threshold_str,
        '{{ target_value }}': _threshold_str,        # alias
        '{{ current_value }}': _current_str,
        '{{ observed_value }}': _current_str,        # alias
        '{{ problem_duration }}': _problem_duration_str,
        '{{ since_problem }}': _since_str,
        '{{ threshold_row }}': _threshold_row,
        '{{ current_value_row }}': _current_row,
        '{{ status_text }}': _status_text,
    }

    sla_metrics = notif_data.get('sla_metrics', [])
    if sla_metrics:
        variables['{{ sla_table }}'] = _build_sla_table_html(
            sla_metrics, notif_data.get('notification_type', '')
        )
    else:
        variables['{{ sla_table }}'] = ''

    subject = template.subject
    body = template.body
    for var, val in variables.items():
        subject = subject.replace(var, val)
        body = body.replace(var, val)

    # For interface notifications, append interface name to subject
    ifname = notif_data.get('ifname', '')
    if ifname and notification.type in ('interface_is_down', 'interface_is_up', 'wan_internet_down', 'wan_internet_up'):
        subject = subject + ' — ' + ifname

    try:
        from django.core.mail import EmailMultiAlternatives
        from django.utils.html import strip_tags

        mail = EmailMultiAlternatives(
            subject=subject,
            body=strip_tags(body),
            from_email=settings.DEFAULT_FROM_EMAIL,
            to=[notification.recipient.email],
        )
        mail.attach_alternative(body, "text/html")
        mail.send()

        notification.emailed = True
        notification._meta.model.objects.bulk_update([notification], fields=["emailed"])
        return True
    except Exception as e:
        logger.warning("Custom template email failed: %s", e)
        return False


def _build_sla_table_html(sla_metrics, notification_type):
    """Build styled HTML table for SLA metrics in email."""
    rows = ""
    for m in sla_metrics:
        status = m.get('status', 'fail')
        if status == 'pass':
            val_style = "color:#16A34A; font-weight:700"
            pill_bg, pill_color, pill_text = "#DCFCE7", "#16A34A", "PASS"
        else:
            val_style = "color:#DC2626; font-weight:700"
            pill_bg, pill_color, pill_text = "#FEE2E2", "#DC2626", "FAIL"
        rows += (
            '<tr>'
            '<td style="padding:10px 14px; border-bottom:1px solid #F1F5F9; font-weight:600; color:#1E293B">%s</td>'
            '<td style="padding:10px 14px; border-bottom:1px solid #F1F5F9; %s">%s</td>'
            '<td style="padding:10px 14px; border-bottom:1px solid #F1F5F9; color:#64748B">%s</td>'
            '<td style="padding:10px 14px; border-bottom:1px solid #F1F5F9; text-align:center">'
            '<span style="display:inline-block; padding:3px 10px; border-radius:999px; font-size:11px; font-weight:700; background:%s; color:%s">%s</span>'
            '</td>'
            '</tr>'
        ) % (m.get("label", ""), val_style, m.get("actual", "N/A"), m.get("target", ""), pill_bg, pill_color, pill_text)

    return (
        '<div style="margin:16px 0">'
        '<table style="width:100%%; border-collapse:collapse; border:1px solid #E5E7EB; border-radius:8px; font-size:13px">'
        '<thead><tr>'
        '<th style="background:#F1F5F9; color:#475569; font-weight:600; text-align:left; padding:10px 14px; border-bottom:2px solid #E2E8F0; font-size:11px; text-transform:uppercase; letter-spacing:0.5px">Metric</th>'
        '<th style="background:#F1F5F9; color:#475569; font-weight:600; text-align:left; padding:10px 14px; border-bottom:2px solid #E2E8F0; font-size:11px; text-transform:uppercase; letter-spacing:0.5px">Actual</th>'
        '<th style="background:#F1F5F9; color:#475569; font-weight:600; text-align:left; padding:10px 14px; border-bottom:2px solid #E2E8F0; font-size:11px; text-transform:uppercase; letter-spacing:0.5px">Target</th>'
        '<th style="background:#F1F5F9; color:#475569; font-weight:600; text-align:center; padding:10px 14px; border-bottom:2px solid #E2E8F0; font-size:11px; text-transform:uppercase; letter-spacing:0.5px">Status</th>'
        '</tr></thead>'
        '<tbody>%s</tbody>'
        '</table>'
        '</div>'
    ) % rows


def _get_device_group_users(target):
    """Check if target device has a group with assigned users.
    Returns a User queryset if group users exist, None otherwise.
    """
    if target is None:
        return None
    try:
        # target must be a Device with a group FK
        group_id = getattr(target, 'group_id', None)
        if not group_id:
            return None
        from swapper import load_model
        DeviceGroupUser = load_model('config', 'DeviceGroupUser')
        user_ids = list(
            DeviceGroupUser.objects.filter(
                device_group_id=group_id
            ).values_list('user_id', flat=True)
        )
        if not user_ids:
            return None  # group exists but no users assigned — fall back to org
        return User.objects.filter(pk__in=user_ids)
    except Exception:
        return None


def notify_handler(**kwargs):
    """
    Handler function to create Notification instance upon action signal call.
    """
    # Pull the options out of kwargs
    kwargs.pop("signal", None)
    actor = kwargs.pop("sender")
    public = bool(kwargs.pop("public", True))
    description = kwargs.pop("description", None)
    timestamp = kwargs.pop("timestamp", timezone.now())
    recipient = kwargs.pop("recipient", None)
    notification_type = kwargs.pop("type", None)
    target = kwargs.get("target", None)
    target_org = getattr(target, "organization_id", None)
    try:
        notification_template = get_notification_configuration(notification_type)
    except NotificationRenderException as error:
        logger.error(f"Error encountered while creating notification: {error}")
        return
    level = kwargs.pop(
        "level", notification_template.get("level", Notification.LEVELS.info)
    )
    verb = notification_template.get("verb", kwargs.pop("verb", None))
    user_app_name = User._meta.app_label

    where = Q(is_superuser=True)
    not_where = Q()
    where_group = Q()
    if target_org:
        # All organization users (not just admins) + superusers
        org_user_query = Q(
            **{
                f"{user_app_name}_organizationuser__organization": target_org,
            }
        )
        where = where | org_user_query
        where_group = org_user_query

        # We can only find notification setting if notification type and
        # target organization is present.
        if notification_type:
            # Create notification for users who have opted for receiving notifications.
            # For users who have not configured web_notifications,
            # use default from notification type
            web_notification = Q(notificationsetting__web=True)
            if notification_template["web_notification"]:
                web_notification |= Q(notificationsetting__web=None)

            notification_setting = web_notification & Q(
                notificationsetting__type=notification_type,
                notificationsetting__organization_id=target_org,
                notificationsetting__deleted=False,
            )
            where = where & notification_setting
            where_group = where_group & notification_setting

    # Ensure notifications are only sent to active user
    where = where & Q(is_active=True)
    where_group = where_group & Q(is_active=True)

    # We can only find ignore notification setting if target object is present
    if target:
        not_where = Q(
            ignoreobjectnotification__object_id=target.pk,
            ignoreobjectnotification__object_content_type=ContentType.objects.get_for_model(
                target._meta.model
            ),
        ) & (
            Q(ignoreobjectnotification__valid_till=None)
            | Q(ignoreobjectnotification__valid_till__gt=timezone.now())
        )

    # If an AlertConfiguration exists for this org+type, the admin's
    # recipient picker overrides the default per-user-preference logic.
    # 'all_org_users' = every active org member (force-deliver, ignoring
    # personal NotificationSetting). 'selected' = only the picked users.
    # Per-user channel flags decide whether each user gets a Web Notification
    # row at all — users with web=False are excluded from the override list
    # so no Notification is created for them on the web side. Email firing
    # is governed by the synced NotificationSetting.email column, which the
    # save handler in alert_config_api keeps in lockstep with the channel
    # flags here.
    ac_override_recipients = None
    if target_org and notification_type:
        try:
            from email_templates.models import AlertConfiguration
            _ac = (
                AlertConfiguration.objects
                .filter(organization_id=target_org, notification_type=notification_type)
                .prefetch_related("selected_recipients")
                .first()
            )
        except Exception:
            _ac = None
        if _ac is not None and _ac.is_enabled:
            try:
                channels = _ac.selected_recipient_channels or {}
                if _ac.recipient_mode == "selected":
                    candidate_users = list(
                        _ac.selected_recipients.filter(is_active=True)
                    )
                    ac_override_recipients = [
                        u for u in candidate_users
                        if channels.get(str(u.pk), {"web": True}).get("web", True)
                    ]
                elif _ac.recipient_mode == "all_org_users":
                    if _ac.all_org_users_web:
                        org_user_ids = User.objects.filter(
                            **{
                                f"{user_app_name}_organizationuser__organization_id": target_org,
                            },
                            is_active=True,
                        ).values_list("pk", flat=True)
                        ac_override_recipients = list(
                            User.objects.filter(pk__in=list(org_user_ids))
                        )
                    else:
                        # All-org with web disabled — no web Notification
                        # created. Email-only is governed by the synced
                        # NotificationSetting.email rows the save handler
                        # writes (see alert_config_api).
                        ac_override_recipients = []
            except Exception as exc:
                logger.warning("AlertConfiguration recipient override failed: %s", exc)

    if recipient:
        # Check if recipient is User, Group or QuerySet
        if isinstance(recipient, Group):
            recipients = recipient.user_set.filter(where_group)
        elif isinstance(recipient, QuerySet):
            recipients = recipient.distinct()
        elif isinstance(recipient, list):
            recipients = recipient
        else:
            recipients = [recipient]
    elif ac_override_recipients is not None:
        recipients = ac_override_recipients
    else:
        # Recipients = org admins + superusers (default) + device group users (if any).
        # Device group users are ADDITIONAL — they get notified only for devices
        # in their assigned group, on top of the default org-level recipients.
        group_users = _get_device_group_users(target)
        if group_users is not None:
            group_user_ids = set(group_users.values_list('pk', flat=True))
            recipients = (
                User.objects.prefetch_related(
                    "notificationsetting_set", "ignoreobjectnotification_set"
                )
                .order_by("date_joined")
                .filter(where | Q(pk__in=group_user_ids))
                .filter(Q(is_active=True))
                .exclude(not_where)
                .distinct()
            )
        else:
            recipients = (
                User.objects.prefetch_related(
                    "notificationsetting_set", "ignoreobjectnotification_set"
                )
                .order_by("date_joined")
                .filter(where)
                .exclude(not_where)
                .distinct()
            )
    optional_objs = [
        (kwargs.pop(opt, None), opt) for opt in ("target", "action_object")
    ]

    notification_list = []
    for recipient in recipients:
        notification = Notification(
            recipient=recipient,
            actor=actor,
            verb=str(verb),
            public=public,
            description=description,
            timestamp=timestamp,
            level=level,
            type=notification_type,
        )

        # Set optional objects
        for obj, opt in optional_objs:
            if obj is not None:
                setattr(notification, "%s_object_id" % opt, obj.pk)
                setattr(
                    notification,
                    "%s_content_type" % opt,
                    ContentType.objects.get_for_model(obj),
                )
        if kwargs and EXTRA_DATA:
            notification.data = kwargs
        notification.save()
        notification_list.append(notification)

    return notification_list


@receiver(post_save, sender=Notification, dispatch_uid="send_email_notification")
def send_email_notification(sender, instance, created, **kwargs):
    # Abort if a new notification is not created
    if not created:
        return

    email_verified = instance.recipient.emailaddress_set.filter(
        verified=True, email=instance.recipient.email
    ).exists()
    if not email_verified or not get_user_email_preference(instance):
        return

    # Check AlertConfiguration for email timing and custom template
    alert_config = _get_alert_config(instance)
    alert_email_timing = alert_config.email_timing if alert_config else None
    if alert_email_timing == "disabled":
        return  # AlertConfig says no email for this type
    # The "immediate" timing was renamed to "keep_default" in the model
    # — both names need to trigger the same path (immediate send + use
    # custom EmailTemplate when AlertConfiguration has one). Without
    # accepting "keep_default" here, configs that picked an email
    # template were silently falling through to the batched/default
    # path and the user got the system default email instead of the
    # template they selected.
    if alert_email_timing in ("keep_default", "immediate", "after_retries", "after_tolerance"):
        # Try custom EmailTemplate first, fall back to default
        if alert_config and alert_config.email_template:
            _send_custom_template_email(instance, alert_config)
        else:
            instance.send_email()
        Notification.set_last_email_sent_time_for_user(
            instance.recipient, instance.timestamp
        )
        return  # bypass batch, send now

    if not app_settings.EMAIL_BATCH_INTERVAL:
        instance.send_email()
        return
    last_email_sent_time, batch_start_time, batched_notifications = (
        Notification.get_user_batch_email_data(instance.recipient)
    )
    # Send a single email if:
    # 1. The user has not received any email yet
    # 2. The last email was sent more than EMAIL_BATCH_INTERVAL seconds ago and
    #    no batch is scheduled
    if not last_email_sent_time or (
        not batch_start_time
        and (
            # More than EMAIL_BATCH_INTERVAL seconds have passed since the last email was sent
            last_email_sent_time
            < (
                timezone.now()
                - timezone.timedelta(seconds=app_settings.EMAIL_BATCH_INTERVAL)
            )
        )
    ):
        instance.send_email()
        Notification.set_last_email_sent_time_for_user(
            instance.recipient, instance.timestamp
        )
        return
    batched_notifications.append(instance.id)
    Notification.set_user_batch_email_data(
        instance.recipient,
        last_email_sent_time=last_email_sent_time,
        start_time=batch_start_time or instance.timestamp,
        pks=batched_notifications,
    )
    # If no batch was scheduled, schedule a new one
    if not batch_start_time:
        tasks.send_batched_email_notifications.apply_async(
            (str(instance.recipient.pk),),
            countdown=app_settings.EMAIL_BATCH_INTERVAL,
        )
    elif (
        batch_start_time
        + timezone.timedelta(seconds=app_settings.EMAIL_BATCH_INTERVAL * 1.25)
    ) < timezone.now():
        # The celery task failed to execute in the expected time.
        # This could happen when the celery worker is overloaded.
        # Send the email immediately.
        tasks.send_batched_email_notifications(
            instance.recipient.pk,
        )


@receiver(post_save, sender=Notification, dispatch_uid="clear_notification_cache_saved")
@receiver(
    post_delete, sender=Notification, dispatch_uid="clear_notification_cache_deleted"
)
def clear_notification_cache(sender, instance, **kwargs):
    Notification.invalidate_unread_cache(instance.recipient)
    # Reload notification widget only if notification is created or deleted
    # Display notification toast when a new notification is created
    ws_handlers.notification_update_handler(
        recipient=instance.recipient,
        reload_widget=kwargs.get("created", True),
        notification=instance if kwargs.get("created", None) else None,
    )


@receiver(post_delete, dispatch_uid="delete_obsolete_objects")
def related_object_deleted(sender, instance, **kwargs):
    """
    Delete Notification and IgnoreObjectNotification objects having
    "instance" as related object.
    """
    if sender not in NOTIFICATION_ASSOCIATED_MODELS:
        return
    instance_id = getattr(instance, "pk", None)
    if instance_id:
        instance_model = instance._meta.model_name
        instance_app_label = instance._meta.app_label
        tasks.delete_obsolete_objects.delay(
            instance_app_label, instance_model, instance_id
        )


def notification_type_registered_unregistered_handler(sender, **kwargs):
    try:
        tasks.ns_register_unregister_notification_type.delay()
    except OperationalError:
        logger.warn(
            "\tCelery broker is unreachable, skipping populating data for user(s) "
            "notification preference(s).\n"
            "\tMake sure that celery broker is running and reachable by celery workers.\n"
            "\tYou can use following command later "
            "to populate data for user(s) notification preference(s).\n\n"
            "\t\t python manage.py populate_notification_preferences\n"
        )


@receiver(
    post_save,
    sender=OrganizationUser,
    dispatch_uid="create_orguser_notification_setting",
)
def organization_user_post_save(instance, created, **kwargs):
    transaction.on_commit(
        lambda: tasks.update_org_user_notificationsetting.delay(
            org_user_id=instance.pk,
            user_id=instance.user_id,
            org_id=instance.organization_id,
            is_org_admin=instance.is_admin,
        )
    )


@receiver(
    post_delete,
    sender=OrganizationUser,
    dispatch_uid="delete_orguser_notification_setting",
)
def notification_setting_delete_org_user(instance, **kwargs):
    tasks.ns_organization_user_deleted.delay(
        user_id=instance.user_id, org_id=instance.organization_id
    )


@receiver(pre_save, sender=User, dispatch_uid="superuser_demoted_notification_setting")
def superuser_status_changed_notification_setting(instance, update_fields, **kwargs):
    """
    If user is demoted from superuser status, then
    remove notification settings for non-managed organizations.

    If user is promoted to superuser, then
    create notification settings for all organizations.
    """
    if update_fields is not None and "is_superuser" not in update_fields:
        # No-op if is_superuser field is not being updated.
        # If update_fields is None, it means any field could be updated.
        return
    try:
        db_instance = User.objects.only("is_superuser").get(pk=instance.pk)
    except User.DoesNotExist:
        # User is being created
        return
    # If user is demoted from superuser to non-superuser
    if db_instance.is_superuser and not instance.is_superuser:
        transaction.on_commit(
            lambda: tasks.superuser_demoted_notification_setting.delay(instance.pk)
        )
    elif not db_instance.is_superuser and instance.is_superuser:
        transaction.on_commit(
            lambda: tasks.create_superuser_notification_settings.delay(instance.pk)
        )


@receiver(post_save, sender=User, dispatch_uid="create_superuser_notification_settings")
def create_superuser_notification_settings(instance, created, **kwargs):
    if created and instance.is_superuser:
        transaction.on_commit(
            lambda: tasks.create_superuser_notification_settings.delay(instance.pk)
        )


@receiver(
    post_save, sender=Organization, dispatch_uid="org_created_notification_setting"
)
def notification_setting_org_created(created, instance, **kwargs):
    if created:
        transaction.on_commit(lambda: tasks.ns_organization_created.delay(instance.pk))


@receiver(
    post_save,
    sender=IgnoreObjectNotification,
    dispatch_uid="schedule_object_notification_deletion",
)
def schedule_object_notification_deletion(instance, created, **kwargs):
    if instance.valid_till is not None:
        tasks.delete_ignore_object_notification.apply_async(
            (instance.pk,), eta=instance.valid_till
        )


def register_notification_cache_update(model, signal, dispatch_uid=None):
    signal.connect(
        update_notification_cache,
        sender=model,
        dispatch_uid=dispatch_uid,
    )


def update_notification_cache(sender, instance, **kwargs):
    def invalidate_cache():
        content_type = ContentType.objects.get_for_model(instance)
        cache_key = Notification._cache_key(content_type.id, instance.id)
        cache.delete(cache_key)

    # execute cache invalidation only after changes have been committed to the DB
    transaction.on_commit(invalidate_cache)


@receiver(user_logged_in)
def check_email_verification(sender, user, request, **kwargs):
    admin_path = reverse("admin:index")
    # abort if this is not an admin login
    if not user.is_staff or not request.path.startswith(admin_path):
        return
    if not NotificationSetting.email_notifications_enabled(user):
        return
    has_verified_email = EmailAddress.objects.filter(user=user, verified=True).exists()
    # abort if user already has a verified email
    # or doesn't have an email at all
    if has_verified_email or not user.email:
        return
    # add a warning UX message encouraging the user
    # to verify his email address
    next_path = request.POST.get(
        "next", request.GET.get("next", reverse("admin:index"))
    )
    current_path = quote(next_path)
    resend_path = reverse("notifications:resend_verification_email")
    resend_url = f"{resend_path}?next={current_path}"
    message = format_html(
        _(
            "Email notifications are enabled, but emails cannot "
            "be sent because your email address is not verified. "
            'Please <a href="{}">verify your email address</a> '
            "to enable email notifications."
        ),
        resend_url,
    )
    messages.warning(request, message)
