/*
 * Asterisk -- An open source telephony toolkit.
 *
 * Copyright (C) 2012, Luka Perkov
 * Copyright (C) 2012, John Crispin
 * Copyright (C) 2012, Andrej Vlašić
 * Copyright (C) 2012, Kaspar Schleiser for T-Labs
 *                     (Deutsche Telekom Innovation Laboratories)
 * Copyright (C) 2012, Mirko Vogt for T-Labs
 *                     (Deutsche Telekom Innovation Laboratories)
 * Copyright (c) 2015, Antonio Eugenio Burriel
 *
 * Luka Perkov <openwrt@lukaperkov.net>
 * John Crispin <blogic@openwrt.org>
 * Andrej Vlašić <andrej.vlasic0@gmail.com>
 * Kaspar Schleiser <kaspar@schleiser.de>
 * Mirko Vogt <mirko@openwrt.org>
 * Antonio Eugenio Burriel <aeburriel@gmail.com>
 *
 * See http://www.asterisk.org for more information about
 * the Asterisk project. Please do not directly contact
 * any of the maintainers of this project for assistance;
 * the project provides a web site, mailing lists and IRC
 * channels for your use.
 *
 * This program is free software, distributed under the terms of
 * the GNU General Public License Version 2. See the LICENSE file
 * at the top of the source tree.
 */

/*! \file
 *
 * \brief Asterisk channel line driver for Lantiq based TAPI boards
 *
 * \author Luka Perkov <openwrt@lukaperkov.net>
 * \author John Crispin <blogic@openwrt.org>
 * \author Andrej Vlašić <andrej.vlasic0@gmail.com>
 * \author Kaspar Schleiser <kaspar@schleiser.de>
 * \author Mirko Vogt <mirko@openwrt.org>
 * \author Antonio Eugenio Burriel <aeburriel@gmail.com>
 * 
 * \ingroup channel_drivers
 */

#include "asterisk.h"

ASTERISK_FILE_VERSION(__FILE__, "$Revision: xxx $")

#include <ctype.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <signal.h>
#include <stdio.h>
#ifdef HAVE_LINUX_COMPILER_H
#include <linux/compiler.h>
#endif
#include <linux/telephony.h>

#include <asterisk/lock.h>
#include <asterisk/channel.h>
#include <asterisk/config.h>
#include <asterisk/module.h>
#include <asterisk/pbx.h>
#include <asterisk/utils.h>
#include <asterisk/callerid.h>
#include <asterisk/causes.h>
#include <asterisk/stringfields.h>
#include <asterisk/musiconhold.h>
#include <asterisk/sched.h>
#include <asterisk/cli.h>
#include <asterisk/devicestate.h>

/* Lantiq TAPI includes */
#include <drv_tapi/drv_tapi_io.h>
#include <drv_vmmc/vmmc_io.h>

#define TAPI_AUDIO_PORT_NUM_MAX                 2
#define TAPI_TONE_LOCALE_NONE                   0 
#define TAPI_TONE_LOCALE_RINGING_CODE           26
#define TAPI_TONE_LOCALE_BUSY_CODE              27
#define TAPI_TONE_LOCALE_CONGESTION_CODE        27
#define TAPI_TONE_LOCALE_DIAL_CODE              25
#define TAPI_TONE_LOCALE_WAITING_CODE           37

#define LANTIQ_CONTEXT_PREFIX "lantiq"
#define DEFAULT_INTERDIGIT_TIMEOUT 2000
#define G723_HIGH_RATE	1

static const char config[] = "lantiq.conf";

static char firmware_filename[PATH_MAX] = "/lib/firmware/ifx_firmware.bin";
static char bbd_filename[PATH_MAX] = "/lib/firmware/ifx_bbd_fxs.bin";
static char base_path[PATH_MAX] = "/dev/vmmc";
static int per_channel_context = 0;

/*
 * The private structures of the Phone Jack channels are linked for selecting
 * outgoing channels.
 */
enum channel_state {
	ONHOOK,
	OFFHOOK,
	DIALING,
	INCALL,
	CALL_ENDED,
	RINGING,
	UNKNOWN
};

static struct lantiq_pvt {
	struct ast_channel *owner;         /* Channel we belong to, possibly NULL   */
	int port_id;                       /* Port number of this object, 0..n      */
	int channel_state;
	char context[AST_MAX_CONTEXT];     /* this port's dialplan context          */
	char ext[AST_MAX_EXTENSION+1];     /* the extension this port is connecting */
	int dial_timer;                    /* timer handle for autodial timeout     */
	char dtmfbuf[AST_MAX_EXTENSION+1]; /* buffer holding dialed digits          */
	int dtmfbuf_len;                   /* lenght of dtmfbuf                     */
	int rtp_timestamp;                 /* timestamp for RTP packets             */
	int ptime;			   /* TAPI base enconder ptime		    */
	format_t codec;			   /* Asterisk codec in use		    */
	char rtp_payload;		   /* Internal RTP payload code in use	    */
	uint16_t rtp_seqno;                /* Sequence nr for RTP packets           */
	uint32_t call_setup_start;         /* Start of dialling in ms               */
	uint32_t call_setup_delay;         /* time between ^ and 1st ring in ms     */
	uint32_t call_start;               /* time we started dialling / answered   */
	uint32_t call_answer;              /* time the callee answered our call     */
	uint16_t jb_size;                  /* Jitter buffer size                    */
	uint32_t jb_underflow;             /* Jitter buffer injected samples        */
	uint32_t jb_overflow;              /* Jitter buffer dropped samples         */
	uint16_t jb_delay;                 /* Jitter buffer: playout delay          */
	uint16_t jb_invalid;               /* Jitter buffer: Nr. of invalid packets */

} *iflist = NULL;

static struct lantiq_ctx {
		int dev_fd;
		int channels;
		int ch_fd[TAPI_AUDIO_PORT_NUM_MAX];
		char *voip_led;                         /* VOIP LED name */
                char *ch_led[TAPI_AUDIO_PORT_NUM_MAX];  /* FXS LED names */
                int interdigit_timeout; /* Timeout in ms between dialed digits */
} dev_ctx = {.voip_led = "voice", .ch_led = {"fxs1", "fxs2"}};

static int ast_digit_begin(struct ast_channel *ast, char digit);
static int ast_digit_end(struct ast_channel *ast, char digit, unsigned int duration);
static int ast_lantiq_call(struct ast_channel *ast, char *dest, int timeout);
static int ast_lantiq_hangup(struct ast_channel *ast);
static int ast_lantiq_answer(struct ast_channel *ast);
static struct ast_frame *ast_lantiq_read(struct ast_channel *ast);
static int ast_lantiq_write(struct ast_channel *ast, struct ast_frame *frame);
static struct ast_frame *ast_lantiq_exception(struct ast_channel *ast);
static int ast_lantiq_indicate(struct ast_channel *chan, int condition, const void *data, size_t datalen);
static int ast_lantiq_fixup(struct ast_channel *old, struct ast_channel *new);
static struct ast_channel *ast_lantiq_requester(const char *type, format_t format, const struct ast_channel *requestor, void *data, int *cause);
static int ast_lantiq_devicestate(void *data);
static int acf_channel_read(struct ast_channel *chan, const char *funcname, char *args, char *buf, size_t buflen);
static void lantiq_jb_get_stats(int c);
static int lantiq_conf_enc(int c, format_t formatid);

static const struct ast_channel_tech lantiq_tech = {
	.type = "TAPI",
	.description = "Lantiq TAPI Telephony API Driver",
	.capabilities = AST_FORMAT_G729A | AST_FORMAT_ULAW | AST_FORMAT_ALAW | AST_FORMAT_G726 | AST_FORMAT_ILBC | AST_FORMAT_SLINEAR | AST_FORMAT_SLINEAR16 | AST_FORMAT_G722 | AST_FORMAT_SIREN7,
	.send_digit_begin = ast_digit_begin,
	.send_digit_end = ast_digit_end,
	.call = ast_lantiq_call,
	.hangup = ast_lantiq_hangup,
	.answer = ast_lantiq_answer,
	.read = ast_lantiq_read,
	.write = ast_lantiq_write,
	.exception = ast_lantiq_exception,
	.indicate = ast_lantiq_indicate,
	.fixup = ast_lantiq_fixup,
	.requester = ast_lantiq_requester,
	.devicestate = ast_lantiq_devicestate,
	.func_channel_read = acf_channel_read
};

/* Protect the interface list (of lantiq_pvt's) */
AST_MUTEX_DEFINE_STATIC(iflock);

/*
 * Protect the monitoring thread, so only one process can kill or start it, and
 * not when it's doing something critical.
 */
AST_MUTEX_DEFINE_STATIC(monlock);

/* The scheduling thread */
struct ast_sched_thread *sched_thread;
   
/*
 * This is the thread for the monitor which checks for input on the channels
 * which are not currently in use.
 */
static pthread_t monitor_thread = AST_PTHREADT_NULL;


#define WORDS_BIGENDIAN
/* struct taken from some GPLed code by  Mike Borella */
typedef struct rtp_header
{
#if defined(WORDS_BIGENDIAN)
  uint8_t version:2, padding:1, extension:1, csrc_count:4;
  uint8_t marker:1, payload_type:7;
#else
  uint8_t csrc_count:4, extension:1, padding:1, version:2;
  uint8_t payload_type:7, marker:1;
#endif
  uint16_t seqno;
  uint32_t timestamp;
  uint32_t ssrc;
} rtp_header_t;
#define RTP_HEADER_LEN 12
#define RTP_BUFFER_LEN 512
/* Internal RTP payload types - standard */
#define RTP_PCMU	0
#define RTP_G723	4
#define RTP_PCMA	8
#define RTP_G722	9
#define RTP_CN		13
#define RTP_G729	18
/* Internal RTP payload types - custom   */
#define RTP_G7221	100
#define RTP_G726	101
#define RTP_ILBC	102
#define RTP_SLIN8	103
#define RTP_SLIN16	104
#define RTP_SIREN7	105


/* LED Control. Taken with modifications from SVD by Luca Olivetti <olivluca@gmail.com> */
#define LED_SLOW_BLINK	1000
#define LED_FAST_BLINK	100
static FILE *led_open(const char *led, char* sub)
{
	char fname[100];

	if (snprintf(fname, sizeof(fname), "/sys/class/leds/%s/%s", led, sub) >= sizeof(fname))
		return NULL;
	return fopen(fname, "r+");
}

static FILE *led_trigger(const char *led)
{
	return led_open(led, "trigger");
}

static void led_delay(const char *led, int onoff, int msec)
{
	FILE *fp = led_open(led, onoff ? "delay_on" : "delay_off");
	if (fp) {
		fprintf(fp,"%d\n",msec);
		fclose(fp);
	}
}

static void led_on(const char *led)
{
	FILE *fp;

	fp = led_trigger(led);
	if (fp) {
		fprintf(fp,"default-on\n");
		fclose(fp);
	}
}

static void led_off(const char *led)
{
	FILE *fp;

	fp = led_trigger(led);
	if (fp) {
		fprintf(fp,"none\n");
		fclose(fp);
	}
}

static void led_blink(const char *led, int period)
{
	FILE *fp;

	fp = led_trigger(led);
	if (fp) {
		fprintf(fp, "timer\n");
		fclose(fp);
		led_delay(led, 1, period/2);
		led_delay(led, 0, period/2);
	}
}

static uint32_t now(void) {
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);

	uint64_t tmp = ts.tv_sec*1000 + (ts.tv_nsec/1000000);
	return (uint32_t) tmp;
}

static uint32_t epoch(void) {
	struct timeval tv;
	gettimeofday(&tv, NULL);

	return tv.tv_sec;
}

static int lantiq_dev_open(const char *dev_path, const int32_t ch_num)
{
	char dev_name[PATH_MAX];
	memset(dev_name, 0, sizeof(dev_name));
	snprintf(dev_name, PATH_MAX, "%s%u%u", dev_path, 1, ch_num);
	return open((const char*)dev_name, O_RDWR, 0644);
}

static void lantiq_ring(int c, int r, const char *cid, const char *name)
{
	uint8_t status;

	if (r) {
		led_blink(dev_ctx.ch_led[c], LED_FAST_BLINK);
		if (!cid) {
			status = (uint8_t) ioctl(dev_ctx.ch_fd[c], IFX_TAPI_RING_START, 0);
		} else {
			IFX_TAPI_CID_MSG_t msg;
			IFX_TAPI_CID_MSG_ELEMENT_t elements[3];
			int count = 0;
			time_t timestamp;
			struct tm *tm;

			elements[count].string.elementType = IFX_TAPI_CID_ST_CLI;
			elements[count].string.len = strlen(cid);
			if (elements[count].string.len > IFX_TAPI_CID_MSG_LEN_MAX) {
				elements[count].string.len = IFX_TAPI_CID_MSG_LEN_MAX;
			}
			strncpy((char *)elements[count++].string.element, cid, IFX_TAPI_CID_MSG_LEN_MAX);

			elements[count].string.elementType = IFX_TAPI_CID_ST_NAME;
			elements[count].string.len = strlen(name);
			if (elements[count].string.len > IFX_TAPI_CID_MSG_LEN_MAX) {
				elements[count].string.len = IFX_TAPI_CID_MSG_LEN_MAX;
			}
			strncpy((char *)elements[count++].string.element, name, IFX_TAPI_CID_MSG_LEN_MAX);

			if ((time(&timestamp) != -1) && ((tm=localtime(&timestamp)) != NULL)) {
				elements[count].date.elementType = IFX_TAPI_CID_ST_DATE;
				elements[count].date.day = tm->tm_mday;
				elements[count].date.month = tm->tm_mon;
				elements[count].date.hour = tm->tm_hour;
				elements[count].date.mn = tm->tm_min;
				count++;
			}

			msg.txMode = IFX_TAPI_CID_HM_ONHOOK;
			msg.messageType = IFX_TAPI_CID_MT_CSUP;
			msg.message = elements;
			msg.nMsgElements = count;

			status = (uint8_t) ioctl(dev_ctx.ch_fd[c], IFX_TAPI_CID_TX_SEQ_START, (IFX_int32_t) &msg);
		}
	} else {
		status = (uint8_t) ioctl(dev_ctx.ch_fd[c], IFX_TAPI_RING_STOP, 0);
		led_off(dev_ctx.ch_led[c]);
	}

	if (status) {
		ast_log(LOG_ERROR, "%s ioctl failed\n",
			(r ? "IFX_TAPI_RING_START" : "IFX_TAPI_RING_STOP"));
	}
}

static int lantiq_play_tone(int c, int t)
{
	/* stop currently playing tone before starting new one */
	if (t != TAPI_TONE_LOCALE_NONE) {
		ioctl(dev_ctx.ch_fd[c], IFX_TAPI_TONE_LOCAL_PLAY, TAPI_TONE_LOCALE_NONE);
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_TONE_LOCAL_PLAY, t)) {
		ast_log(LOG_DEBUG, "IFX_TAPI_TONE_LOCAL_PLAY ioctl failed\n");
		return -1;
	}

	return 0;
}

static enum channel_state lantiq_get_hookstatus(int port)
{
	uint8_t status;

	if (ioctl(dev_ctx.ch_fd[port], IFX_TAPI_LINE_HOOK_STATUS_GET, &status)) {
		ast_log(LOG_ERROR, "IFX_TAPI_LINE_HOOK_STATUS_GET ioctl failed\n");
		return UNKNOWN;
	}

	if (status) {
		return OFFHOOK;
	} else {
		return ONHOOK;
	}
}

static int
lantiq_dev_binary_buffer_create(const char *path, uint8_t **ppBuf, uint32_t *pBufSz)
{
	FILE *fd;
	struct stat file_stat;
	int32_t status = 0;

	fd = fopen(path, "rb");
	if (fd == NULL) {
		ast_log(LOG_ERROR, "binary file %s open failed\n", path);
		return -1;
	}

	if (stat(path, &file_stat)) {
		ast_log(LOG_ERROR, "file %s statistics get failed\n", path);
		return -1;
	}

	*ppBuf = malloc(file_stat.st_size);
	if (*ppBuf == NULL) {
		ast_log(LOG_ERROR, "binary file %s memory allocation failed\n", path);
		status = -1;
		goto on_exit;
	}

	if (fread (*ppBuf, sizeof(uint8_t), file_stat.st_size, fd) <= 0) {
		ast_log(LOG_ERROR, "file %s read failed\n", path);
		status = -1;
		goto on_exit;
	}

	*pBufSz = file_stat.st_size;

on_exit:
	if (fd != NULL)
		fclose(fd);

	if (*ppBuf != NULL && status)
		free(*ppBuf);

	return status;
}

static int32_t lantiq_dev_firmware_download(int32_t fd, const char *path)
{
	uint8_t *firmware = NULL;
	uint32_t size = 0;
	VMMC_IO_INIT vmmc_io_init;

	ast_log(LOG_DEBUG, "loading firmware: \"%s\".\n", path);

	if (lantiq_dev_binary_buffer_create(path, &firmware, &size))
		return -1;

	memset(&vmmc_io_init, 0, sizeof(VMMC_IO_INIT));
	vmmc_io_init.pPRAMfw = firmware;
	vmmc_io_init.pram_size = size;

	if (ioctl(fd, FIO_FW_DOWNLOAD, &vmmc_io_init)) {
		ast_log(LOG_ERROR, "FIO_FW_DOWNLOAD ioctl failed\n");
		return -1;
	}

	if (firmware != NULL)
		free(firmware);

	return 0;
}

static const char *state_string(enum channel_state s)
{
	switch (s) {
		case ONHOOK: return "ONHOOK";
		case OFFHOOK: return "OFFHOOK";
		case DIALING: return "DIALING";
		case INCALL: return "INCALL";
		case CALL_ENDED: return "CALL_ENDED";
		case RINGING: return "RINGING";
		default: return "UNKNOWN";
	}
}

static const char *control_string(int c)
{
	switch (c) {
		case AST_CONTROL_HANGUP: return "Other end has hungup";
		case AST_CONTROL_RING: return "Local ring";
		case AST_CONTROL_RINGING: return "Remote end is ringing";
		case AST_CONTROL_ANSWER: return "Remote end has answered";
		case AST_CONTROL_BUSY: return "Remote end is busy";
		case AST_CONTROL_TAKEOFFHOOK: return "Make it go off hook";
		case AST_CONTROL_OFFHOOK: return "Line is off hook";
		case AST_CONTROL_CONGESTION: return "Congestion (circuits busy)";
		case AST_CONTROL_FLASH: return "Flash hook";
		case AST_CONTROL_WINK: return "Wink";
		case AST_CONTROL_OPTION: return "Set a low-level option";
		case AST_CONTROL_RADIO_KEY: return "Key Radio";
		case AST_CONTROL_RADIO_UNKEY: return "Un-Key Radio";
		case AST_CONTROL_PROGRESS: return "Remote end is making Progress";
		case AST_CONTROL_PROCEEDING: return "Remote end is proceeding";
		case AST_CONTROL_HOLD: return "Hold";
		case AST_CONTROL_UNHOLD: return "Unhold";
		case AST_CONTROL_SRCUPDATE: return "Media Source Update";
		case AST_CONTROL_CONNECTED_LINE: return "Connected Line";
		case AST_CONTROL_REDIRECTING: return "Redirecting";
		case AST_CONTROL_INCOMPLETE: return "Incomplete";
		case -1: return "Stop tone";
		default: return "Unknown";
	}
}

static int ast_lantiq_indicate(struct ast_channel *chan, int condition, const void *data, size_t datalen)
{
	ast_verb(3, "phone indication \"%s\"\n", control_string(condition));

	struct lantiq_pvt *pvt = chan->tech_pvt;

	switch (condition) {
		case -1:
			{
				lantiq_play_tone(pvt->port_id, TAPI_TONE_LOCALE_NONE);
				return 0;
			}
		case AST_CONTROL_CONGESTION:
		case AST_CONTROL_BUSY:
			{
				lantiq_play_tone(pvt->port_id, TAPI_TONE_LOCALE_BUSY_CODE);
				return 0;
			}
		case AST_CONTROL_RINGING:
		case AST_CONTROL_PROGRESS:
			{
				pvt->call_setup_delay = now() - pvt->call_setup_start;
				lantiq_play_tone(pvt->port_id, TAPI_TONE_LOCALE_RINGING_CODE);
				return 0;
			}
		default:
			{
				/* -1 lets asterisk generate the tone */
				return -1;
			}
	}
}

static int ast_lantiq_fixup(struct ast_channel *old, struct ast_channel *new)
{
	ast_log(LOG_DEBUG, "entering... no code here...\n");
	return 0;
}

static int ast_digit_begin(struct ast_channel *chan, char digit)
{
	/* TODO: Modify this callback to let Asterisk support controlling the length of DTMF */
	ast_log(LOG_DEBUG, "entering... no code here...\n");
	return 0;
}

static int ast_digit_end(struct ast_channel *ast, char digit, unsigned int duration)
{
	ast_log(LOG_DEBUG, "entering... no code here...\n");
	return 0;
}

static int ast_lantiq_call(struct ast_channel *ast, char *dest, int timeout)
{
	int res = 0;

	/* lock to prevent simultaneous access with do_monitor thread processing */
	ast_mutex_lock(&iflock);

	struct lantiq_pvt *pvt = ast->tech_pvt;
	ast_log(LOG_DEBUG, "state: %s\n", state_string(pvt->channel_state));

	if (pvt->channel_state == ONHOOK) {
		ast_log(LOG_DEBUG, "port %i is ringing\n", pvt->port_id);

		const char *cid = ast->connected.id.number.valid ? ast->connected.id.number.str : NULL;
		const char *name = ast->connected.id.name.valid ? ast->connected.id.name.str : NULL;
		ast_log(LOG_DEBUG, "port %i CID: %s <%s>\n", pvt->port_id, cid ? cid : "none", name ? name : "");

		lantiq_ring(pvt->port_id, 1, cid, name);
		pvt->channel_state = RINGING;

		ast_setstate(ast, AST_STATE_RINGING);
		ast_queue_control(ast, AST_CONTROL_RINGING);
	} else {
		ast_log(LOG_DEBUG, "port %i is busy\n", pvt->port_id);
		ast_setstate(ast, AST_STATE_BUSY);
		ast_queue_control(ast, AST_CONTROL_BUSY);
		res = -1;
	}

	ast_mutex_unlock(&iflock);

	return res;
}

static int ast_lantiq_hangup(struct ast_channel *ast)
{
	/* lock to prevent simultaneous access with do_monitor thread processing */
	ast_mutex_lock(&iflock);

	struct lantiq_pvt *pvt = ast->tech_pvt;
	ast_log(LOG_DEBUG, "state: %s\n", state_string(pvt->channel_state));
	
	if (ast->_state == AST_STATE_RINGING) {
		// FIXME
		ast_debug(1, "TAPI: ast_lantiq_hangup(): ast->_state == AST_STATE_RINGING\n");
	}

	switch (pvt->channel_state) {
		case RINGING:
		case ONHOOK: 
			lantiq_ring(pvt->port_id, 0, NULL, NULL);
			pvt->channel_state = ONHOOK;
			break;
		default:
			ast_log(LOG_DEBUG, "we were hung up, play busy tone\n");
			pvt->channel_state = CALL_ENDED;
			lantiq_play_tone(pvt->port_id, TAPI_TONE_LOCALE_BUSY_CODE);
	}

	lantiq_jb_get_stats(pvt->port_id);

	ast_setstate(ast, AST_STATE_DOWN);
	ast_module_unref(ast_module_info->self);
	ast->tech_pvt = NULL;
	pvt->owner = NULL;

	ast_mutex_unlock(&iflock);

	return 0;
}

static int ast_lantiq_answer(struct ast_channel *ast)
{
	ast_log(LOG_DEBUG, "Remote end has answered call.\n");
	struct lantiq_pvt *pvt = ast->tech_pvt;

	if (lantiq_conf_enc(pvt->port_id, ast->writeformat))
		return -1;

	pvt->call_answer = epoch();
	return 0;
}

static struct ast_frame * ast_lantiq_read(struct ast_channel *ast)
{
	ast_log(LOG_DEBUG, "entering... no code here...\n");
	return NULL;
}

static int lantiq_conf_enc(int c, format_t formatid)
{
	/* Configure encoder before starting RTP session */
	IFX_TAPI_ENC_CFG_t enc_cfg;

	memset(&enc_cfg, 0, sizeof(IFX_TAPI_ENC_CFG_t));
	switch (formatid) {
		case AST_FORMAT_G723_1:
#if defined G723_HIGH_RATE
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_G723_63;
#else
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_G723_53;
#endif
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_30;
			iflist[c].rtp_payload = RTP_G723;
			break;
		case AST_FORMAT_G729A:
			 enc_cfg.nEncType = IFX_TAPI_COD_TYPE_G729;
			 enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_10;
			 iflist[c].rtp_payload = RTP_G729;
			 break;
		case AST_FORMAT_ULAW:
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_MLAW;
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_10;
			iflist[c].rtp_payload = RTP_PCMU;
			break;
		case AST_FORMAT_ALAW:
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_ALAW;
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_10;
			iflist[c].rtp_payload = RTP_PCMA;
			break;
		case AST_FORMAT_G726:
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_G726_32;
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_10;
			iflist[c].rtp_payload = RTP_G726;
			break;
		case AST_FORMAT_ILBC:
			/* iLBC 15.2kbps is currently unsupported by Asterisk */
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_ILBC_133;
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_30;
			iflist[c].rtp_payload = RTP_ILBC;
			break;
		case AST_FORMAT_SLINEAR:
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_LIN16_8;
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_10;
			iflist[c].rtp_payload = RTP_SLIN8;
			break;
		case AST_FORMAT_SLINEAR16:
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_LIN16_16;
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_10;
			iflist[c].rtp_payload = RTP_SLIN16;
			break;
		case AST_FORMAT_G722:
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_G722_64;
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_20;
			iflist[c].rtp_payload = RTP_G722;
			break;
		case AST_FORMAT_SIREN7:
			enc_cfg.nEncType = IFX_TAPI_COD_TYPE_G7221_32;
			enc_cfg.nFrameLen = IFX_TAPI_COD_LENGTH_20;
			iflist[c].rtp_payload = RTP_SIREN7;
			break;
		default:
			ast_log(LOG_ERROR, "unsupported format %llu (%s)\n", formatid, ast_getformatname(formatid));
			return -1;
	}
	iflist[c].codec = formatid;
	ast_log(LOG_DEBUG, "Configuring encoder to use TAPI codec type %d on channel %i\n", enc_cfg.nEncType, c);

	switch (enc_cfg.nFrameLen) {
		case IFX_TAPI_COD_LENGTH_5:
			iflist[c].ptime = 5;
			break;
		case IFX_TAPI_COD_LENGTH_10:
			iflist[c].ptime = 10;
			break;
		case IFX_TAPI_COD_LENGTH_11:
			iflist[c].ptime = 11;
			break;
		case IFX_TAPI_COD_LENGTH_20:
			iflist[c].ptime = 20;
			break;
		case IFX_TAPI_COD_LENGTH_30:
			iflist[c].ptime = 30;
			break;
		case IFX_TAPI_COD_LENGTH_40:
			iflist[c].ptime = 40;
			break;
		case IFX_TAPI_COD_LENGTH_50:
			iflist[c].ptime = 50;
			break;
		case IFX_TAPI_COD_LENGTH_60:
			iflist[c].ptime = 60;
			break;
		default:
			ast_log(LOG_ERROR, "Unsupported TAPI ptime id %d\n", enc_cfg.nFrameLen);
			return -1;
	}
	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_CFG_SET, &enc_cfg)) {
		ast_log(LOG_ERROR, "IFX_TAPI_ENC_CFG_SET %d failed\n", c);
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_START, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_ENC_START ioctl failed\n");
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_DEC_START, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEC_START ioctl failed\n");
	}

	return 0;
}


static int ast_lantiq_write(struct ast_channel *ast, struct ast_frame *frame)
{
	char buf[RTP_BUFFER_LEN];
	rtp_header_t *rtp_header = (rtp_header_t *) buf;
	struct lantiq_pvt *pvt = ast->tech_pvt;
	int subframes, subframe_samples, subframe_size, occupied;
	char *source;
	int ret;

	if(frame->frametype != AST_FRAME_VOICE) {
		ast_log(LOG_DEBUG, "unhandled frame type\n");
		return 0;
	}

	if(frame->subclass.codec != pvt->codec) {
		ast_debug(1, "Received AST voice frame type %llu (%s) but %s was expected.\n", frame->subclass.codec, ast_getformatname(frame->subclass.codec), ast_getformatname(pvt->codec));
		return 0;
	}

	if (frame->datalen == 0) {
		ast_log(LOG_DEBUG, "we've been prodded\n");
		return 0;
	}

	rtp_header->version      = 2;
	rtp_header->padding      = 0;
	rtp_header->extension    = 0;
	rtp_header->csrc_count   = 0;
	rtp_header->marker       = 0;
	rtp_header->ssrc         = 0;
	rtp_header->payload_type = pvt->rtp_payload;

	subframes = frame->len / iflist[pvt->port_id].ptime;
	if (subframes == 0)
		subframes = 1;
	/* These won't work with VBR codecs, fortunately Lantiq doesn't have them */
	subframe_samples = frame->samples / subframes;
	subframe_size = frame->datalen / subframes;
	source = frame->data.ptr;

	while (subframes > 0) {
		occupied = 0;
		rtp_header->seqno        = pvt->rtp_seqno++;
		rtp_header->timestamp    = pvt->rtp_timestamp;

		if( (occupied + subframe_size) > frame->samples) {
			/* In last subframe, should only happen with bitstream codec with non multiple ptime */
			subframe_samples %= subframe_size;
			subframe_size %= frame->datalen;
		}

		while ((subframes > 0) && ((occupied + subframe_size) < (RTP_BUFFER_LEN - RTP_HEADER_LEN))) {
			memcpy(&buf[RTP_HEADER_LEN + occupied], source, subframe_size);
			occupied += subframe_size;
			source += subframe_size;
			subframes--;
			pvt->rtp_timestamp += (rtp_header->payload_type == RTP_G722) ? subframe_samples / 2 : subframe_samples; /* per RFC3551 */
		}

		ret = write(dev_ctx.ch_fd[pvt->port_id], buf, RTP_HEADER_LEN + occupied);
		if (ret < 0) {
			ast_debug(1, "TAPI: ast_lantiq_write(): error writing.\n");
			return -1;
		}
		if (ret != (RTP_HEADER_LEN + occupied)) {
			ast_log(LOG_WARNING, "Short TAPI write of %d bytes, expected %d bytes\n", ret, RTP_HEADER_LEN + occupied);
			continue;
		}

#ifdef TODO_DEVEL_INFO
		ast_debug(1, "ast_lantiq_write(): size: %i version: %i padding: %i extension: %i csrc_count: %i\n"
			 "marker: %i payload_type: %s seqno: %i timestamp: %i ssrc: %i\n",
				 (int)ret,
				 (int)rtp_header->version,
				 (int)rtp_header->padding,
				 (int)rtp_header->extension,
				 (int)rtp_header->csrc_count,
				 (int)rtp_header->marker,
				 ast_codec2str(frame->subclass.codec),
				 (int)rtp_header->seqno,
				 (int)rtp_header->timestamp,
				 (int)rtp_header->ssrc);
#endif
	}

	return 0;
}

static int acf_channel_read(struct ast_channel *chan, const char *funcname, char *args, char *buf, size_t buflen)
{
	struct lantiq_pvt *pvt;
	int res = 0;

	if (!chan || chan->tech != &lantiq_tech) {
		ast_log(LOG_ERROR, "This function requires a valid Lantiq TAPI channel\n");
		return -1;
	}

	ast_mutex_lock(&iflock);

	pvt = (struct lantiq_pvt*) chan->tech_pvt;

	if (!strcasecmp(args, "csd")) {
		snprintf(buf, buflen, "%lu", (unsigned long int) pvt->call_setup_delay);
	} else if (!strcasecmp(args, "jitter_stats")){
		lantiq_jb_get_stats(pvt->port_id);
		snprintf(buf, buflen, "jbBufSize=%u,jbUnderflow=%u,jbOverflow=%u,jbDelay=%u,jbInvalid=%u",
				(uint32_t) pvt->jb_size,
				(uint32_t) pvt->jb_underflow,
				(uint32_t) pvt->jb_overflow,
				(uint32_t) pvt->jb_delay,
				(uint32_t) pvt->jb_invalid);
	} else if (!strcasecmp(args, "jbBufSize")) {
		snprintf(buf, buflen, "%u", (uint32_t) pvt->jb_size);
	} else if (!strcasecmp(args, "jbUnderflow")) {
		snprintf(buf, buflen, "%u", (uint32_t) pvt->jb_underflow);
	} else if (!strcasecmp(args, "jbOverflow")) {
		snprintf(buf, buflen, "%u", (uint32_t) pvt->jb_overflow);
	} else if (!strcasecmp(args, "jbDelay")) {
		snprintf(buf, buflen, "%u", (uint32_t) pvt->jb_delay);
	} else if (!strcasecmp(args, "jbInvalid")) {
		snprintf(buf, buflen, "%u", (uint32_t) pvt->jb_invalid);
	} else if (!strcasecmp(args, "start")) {
		struct tm *tm = gmtime((const time_t*)&pvt->call_start);
		strftime(buf, buflen, "%F %T", tm);
	} else if (!strcasecmp(args, "answer")) {
		struct tm *tm = gmtime((const time_t*)&pvt->call_answer);
		strftime(buf, buflen, "%F %T", tm);
	} else {
		res = -1;
	}

	ast_mutex_unlock(&iflock);

	return res;
}


static struct ast_frame * ast_lantiq_exception(struct ast_channel *ast)
{
	ast_log(LOG_DEBUG, "entering... no code here...\n");
	return NULL;
}

static void lantiq_jb_get_stats(int c) {
	struct lantiq_pvt *pvt = &iflist[c];

	IFX_TAPI_JB_STATISTICS_t param;
	memset (&param, 0, sizeof (param));
	if (ioctl (dev_ctx.ch_fd[c], IFX_TAPI_JB_STATISTICS_GET, (IFX_int32_t) &param) != IFX_SUCCESS) {
		ast_debug(1, "Error getting jitter buffer  stats.\n");
	} else {
#if !defined (TAPI_VERSION3) && defined (TAPI_VERSION4)
		ast_debug(1, "Jitter buffer stats:  dev=%u, ch=%u, nType=%u, nBufSize=%u, nIsUnderflow=%u, nDsOverflow=%u, nPODelay=%u, nInvalid=%u\n", 
				(uint32_t) param.dev,
				(uint32_t) param.ch,
#else
		ast_debug(1, "Jitter buffer stats:  nType=%u, nBufSize=%u, nIsUnderflow=%u, nDsOverflow=%u, nPODelay=%u, nInvalid=%u\n", 
#endif
				(uint32_t) param.nType,
				(uint32_t) param.nBufSize,
				(uint32_t) param.nIsUnderflow,
				(uint32_t) param.nDsOverflow,
				(uint32_t) param.nPODelay,
				(uint32_t) param.nInvalid);
		
		pvt->jb_size = param.nBufSize;
		pvt->jb_underflow = param.nIsUnderflow;
		pvt->jb_overflow = param.nDsOverflow;
		pvt->jb_invalid = param.nInvalid;
		pvt->jb_delay = param.nPODelay;
	}
}


static int lantiq_standby(int c)
{
	ast_debug(1, "Stopping line feed for channel %i\n", c);
	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_STANDBY)) {
		ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET ioctl failed\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_STOP, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_ENC_STOP ioctl failed\n");
		return -1;
	}

	if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_DEC_STOP, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEC_STOP ioctl failed\n");
		return -1;
	}

	return lantiq_play_tone(c, TAPI_TONE_LOCALE_NONE);
}

static int lantiq_end_dialing(int c)
{
	ast_log(LOG_DEBUG, "TODO - DEBUG MSG\n");
	struct lantiq_pvt *pvt = &iflist[c];

	if (pvt->dial_timer) {
		ast_sched_thread_del(sched_thread, pvt->dial_timer);
		pvt->dial_timer = 0;
	}

	if(pvt->owner) {
		ast_hangup(pvt->owner);
	}

	return 0;
}

static int lantiq_end_call(int c)
{
	ast_log(LOG_DEBUG, "TODO - DEBUG MSG\n");

	struct lantiq_pvt *pvt = &iflist[c];
	
	if(pvt->owner) {
		lantiq_jb_get_stats(c);
		ast_queue_hangup(pvt->owner);
	}

	return 0;
}

static struct ast_channel * lantiq_channel(int state, int c, char *ext, char *ctx, format_t format)
{
	struct ast_channel *chan = NULL;
	struct lantiq_pvt *pvt = &iflist[c];

	chan = ast_channel_alloc(1, state, NULL, NULL, "", ext, ctx, 0, c, "TAPI/%d", c + 1);
	if (! chan) {
		ast_log(LOG_DEBUG, "Cannot allocate channel!\n");
		return NULL;
	}
/*
	char buf[BUFSIZ];
	if (format != 0 && ! (format & lantiq_tech.capabilities)) {
		ast_log(LOG_WARNING, "Requested channel with unsupported format %s. Forcing ALAW.\n", ast_getformatname_multiple(buf, sizeof(buf), format));
		format = AST_FORMAT_ALAW;
	} else {
		format = lantiq_tech.capabilities;
	}
*/
	chan->tech = &lantiq_tech;
	chan->nativeformats = lantiq_tech.capabilities;
	chan->tech_pvt = pvt;

	pvt->owner = chan;

	if (format != 0)
		if (lantiq_conf_enc(c, format) < 0)
			return NULL;

	return chan;
}

static struct ast_channel * ast_lantiq_requester(const char *type, format_t format, const struct ast_channel *requestor, void *data, int *cause)
{
	ast_mutex_lock(&iflock);

	char buf[BUFSIZ];
	struct ast_channel *chan = NULL;
	int port_id = -1;

	ast_debug(1, "Asked to create a TAPI channel with formats: %s\n", ast_getformatname_multiple(buf, sizeof(buf), format));


	/* check for correct data argument */
	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "Unable to create channel with empty destination.\n");
		*cause = AST_CAUSE_CHANNEL_UNACCEPTABLE;
		goto bailout;
	}

	/* get our port number */
	port_id = atoi((char*) data);
	if (port_id < 1 || port_id > dev_ctx.channels) {
		ast_log(LOG_ERROR, "Unknown channel ID: \"%s\"\n", (char*) data);
		*cause = AST_CAUSE_CHANNEL_UNACCEPTABLE;
		goto bailout;
	}

	/* on asterisk user's side, we're using port 1-2.
	 * Here in non normal human's world, we begin
	 * counting at 0.
	 */
	port_id -= 1;


	/* Bail out if channel is already in use */
	struct lantiq_pvt *pvt = &iflist[port_id];
	if (! pvt->channel_state == ONHOOK) {
		ast_debug(1, "TAPI channel %i alread in use.\n", port_id+1);
	} else {
		chan = lantiq_channel(AST_STATE_DOWN, port_id, NULL, NULL, format);
	}

bailout:
	ast_mutex_unlock(&iflock);
	return chan;
}

static int ast_lantiq_devicestate(void *data)
{
	int port = atoi((char *) data) - 1;
	if ((port < 1) || (port > dev_ctx.channels)) {
		return AST_DEVICE_INVALID;
	}

	switch (iflist[port].channel_state) {
		case ONHOOK:
			return AST_DEVICE_NOT_INUSE;
		case OFFHOOK:
		case DIALING:
		case INCALL:
		case CALL_ENDED:
			return AST_DEVICE_INUSE;
		case RINGING:
			return AST_DEVICE_RINGING;
		case UNKNOWN:
		default:
			return AST_DEVICE_UNKNOWN;
	}
}

static int lantiq_dev_data_handler(int c)
{
	char buf[BUFSIZ];
	struct ast_frame frame = {0};

	int res = read(dev_ctx.ch_fd[c], buf, sizeof(buf));
	if (res <= 0) {
		ast_log(LOG_ERROR, "we got read error %i\n", res);
		return 0;
	}

	rtp_header_t *rtp = (rtp_header_t*) buf;
	struct lantiq_pvt *pvt = (struct lantiq_pvt *) &iflist[c];
	if ((!pvt->owner) || (pvt->owner->_state != AST_STATE_UP)) {
		return 0;
	}

	if(rtp->payload_type != pvt->rtp_payload) {
		if (rtp->payload_type == RTP_CN) {
			/* TODO: Handle Comfort Noise frames */
			ast_debug(1, "Dropping Comfort Noise frame\n");
		}
		ast_debug(1, "Received RTP payload type %d but %d was expected.\n", rtp->payload_type, pvt->rtp_payload);
		return 0;
	}

	frame.src = "TAPI";
	frame.frametype = AST_FRAME_VOICE;
	frame.subclass.codec = pvt->codec;
	frame.datalen = res - RTP_HEADER_LEN;
	frame.data.ptr = buf + RTP_HEADER_LEN;
	frame.samples = ast_codec_get_samples(&frame);

	if(!ast_channel_trylock(pvt->owner)) {
		ast_queue_frame(pvt->owner, &frame);
		ast_channel_unlock(pvt->owner);
	}

/*	ast_debug(1, "lantiq_dev_data_handler(): size: %i version: %i padding: %i extension: %i csrc_count: %i \n"
				 "marker: %i payload_type: %s seqno: %i timestamp: %i ssrc: %i\n", 
				 (int)res,
				 (int)rtp->version,
				 (int)rtp->padding,
				 (int)rtp->extension,
				 (int)rtp->csrc_count,
				 (int)rtp->marker,
				 ast_codec2str(frame.subclass.codec),
				 (int)rtp->seqno,
				 (int)rtp->timestamp,
				 (int)rtp->ssrc);
*/
	return 0;
}

static int accept_call(int c)
{ 
	ast_log(LOG_DEBUG, "TODO - DEBUG MSG\n");

	struct lantiq_pvt *pvt = &iflist[c];

	if (pvt->owner) {
		struct ast_channel *chan = pvt->owner;

		switch (chan->_state) {
			case AST_STATE_RINGING:
				lantiq_play_tone(c, TAPI_TONE_LOCALE_NONE);
				ast_queue_control(pvt->owner, AST_CONTROL_ANSWER);
				pvt->channel_state = INCALL;
				pvt->call_start = epoch();
				pvt->call_answer = pvt->call_start;
				break;
			default:
				ast_log(LOG_WARNING, "entered unhandled state %s\n", ast_state2str(chan->_state));
		}
	}

	return 0;
}

static int lantiq_dev_event_hook(int c, int state)
{
	ast_mutex_lock(&iflock);

	ast_log(LOG_DEBUG, "on port %i detected event %s hook\n", c, state ? "on" : "off");

	int ret = -1;
	if (state) { /* going onhook */
		switch (iflist[c].channel_state) {
			case DIALING: 
				ret = lantiq_end_dialing(c);
				break;
			case INCALL: 
				ret = lantiq_end_call(c);
				break;
		}

		iflist[c].channel_state = ONHOOK;

		/* stop DSP data feed */
		lantiq_standby(c);
		led_off(dev_ctx.ch_led[c]);

	} else { /* going offhook */
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_ACTIVE)) {
			ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET ioctl failed\n");
			goto out;
		}

		switch (iflist[c].channel_state) {
			case RINGING: 
				ret = accept_call(c);
				led_blink(dev_ctx.ch_led[c], LED_SLOW_BLINK);
				break;
			default:
				iflist[c].channel_state = OFFHOOK;
				lantiq_play_tone(c, TAPI_TONE_LOCALE_DIAL_CODE);
				ret = 0;
				led_on(dev_ctx.ch_led[c]);
				break;
		}

	}

out:
	ast_mutex_unlock(&iflock);

	return ret;
}

static void lantiq_reset_dtmfbuf(struct lantiq_pvt *pvt)
{
	pvt->dtmfbuf[0] = '\0';
	pvt->dtmfbuf_len = 0;
	pvt->ext[0] = '\0';
}

static void lantiq_dial(struct lantiq_pvt *pvt)
{
	struct ast_channel *chan = NULL;

	ast_log(LOG_DEBUG, "user want's to dial %s.\n", pvt->dtmfbuf);

	if (ast_exists_extension(NULL, pvt->context, pvt->dtmfbuf, 1, NULL)) {
		ast_debug(1, "found extension %s, dialing\n", pvt->dtmfbuf);

		strcpy(pvt->ext, pvt->dtmfbuf);

		ast_verbose(VERBOSE_PREFIX_3 " extension exists, starting PBX %s\n", pvt->ext);

		chan = lantiq_channel(AST_STATE_UP, pvt->port_id, pvt->ext+1, pvt->context, 0);
		if (!chan) {
			ast_log(LOG_ERROR, "couldn't create channel\n");
			return;
		}
		chan->tech_pvt = pvt;
		pvt->owner = chan;

		strcpy(chan->exten, pvt->ext);
		ast_setstate(chan, AST_STATE_RING);
		pvt->channel_state = INCALL;

		pvt->call_setup_start = now();
		pvt->call_start = epoch();;

		if (ast_pbx_start(chan)) {
			ast_log(LOG_WARNING, " unable to start PBX on %s\n", chan->name);
			ast_hangup(chan);
		}
	} else {
		ast_log(LOG_DEBUG, "no extension found\n");
		lantiq_play_tone(pvt->port_id, TAPI_TONE_LOCALE_BUSY_CODE);
		pvt->channel_state = CALL_ENDED;
	}
	
	lantiq_reset_dtmfbuf(pvt);
}

static int lantiq_event_dial_timeout(const void* data)
{
	ast_debug(1, "TAPI: lantiq_event_dial_timeout()\n");

	struct lantiq_pvt *pvt = (struct lantiq_pvt *) data;
	pvt->dial_timer = 0;

	if (! pvt->channel_state == ONHOOK) {
		lantiq_dial(pvt);
	} else {
		ast_debug(1, "TAPI: lantiq_event_dial_timeout(): dial timeout in state ONHOOK.\n");
	}

	return 0;
}

static int lantiq_send_digit(int c, char digit) 
{
	struct lantiq_pvt *pvt = &iflist[c];

	struct ast_frame f = { .frametype = AST_FRAME_DTMF, .subclass.integer = digit };

	if (pvt->owner) {
		ast_log(LOG_DEBUG, "Port %i transmitting digit \"%c\"\n", c, digit);
		return ast_queue_frame(pvt->owner, &f);
	} else {
		ast_debug(1, "Warning: lantiq_send_digit() without owner!\n");
		return -1;
	}
}

static void lantiq_dev_event_digit(int c, char digit)
{
	ast_mutex_lock(&iflock);

	ast_log(LOG_DEBUG, "on port %i detected digit \"%c\"\n", c, digit);

	struct lantiq_pvt *pvt = &iflist[c];

	switch (pvt->channel_state) {
		case INCALL:
			{
				lantiq_send_digit(c, digit);
				break;
			}
		case OFFHOOK:  
			pvt->channel_state = DIALING;

			lantiq_play_tone(c, TAPI_TONE_LOCALE_NONE);
			led_blink(dev_ctx.ch_led[c], LED_SLOW_BLINK);

			/* fall through */
		case DIALING: 
			if (digit == '#') {
				if (pvt->dial_timer) {
					ast_sched_thread_del(sched_thread, pvt->dial_timer);
					pvt->dial_timer = 0;
				}

				lantiq_dial(pvt);
			} else {
				pvt->dtmfbuf[pvt->dtmfbuf_len] = digit;
				pvt->dtmfbuf_len++;
				pvt->dtmfbuf[pvt->dtmfbuf_len] = '\0';

				/* setup autodial timer */
				if (!pvt->dial_timer) {
					ast_log(LOG_DEBUG, "setting new timer\n");
					pvt->dial_timer = ast_sched_thread_add(sched_thread, dev_ctx.interdigit_timeout, lantiq_event_dial_timeout, (const void*) pvt);
				} else {
					ast_log(LOG_DEBUG, "replacing timer\n");
					struct sched_context *sched = ast_sched_thread_get_context(sched_thread);
					AST_SCHED_REPLACE(pvt->dial_timer, sched, dev_ctx.interdigit_timeout, lantiq_event_dial_timeout, (const void*) pvt);
				}
			}
			break;
		default:
			ast_log(LOG_ERROR, "don't know what to do in unhandled state\n");
			break;
	}

	ast_mutex_unlock(&iflock);
	return;
}

static void lantiq_dev_event_handler(void)
{
	IFX_TAPI_EVENT_t event;
	unsigned int i;

	for (i = 0; i < dev_ctx.channels ; i++) {
		ast_mutex_lock(&iflock);

		memset (&event, 0, sizeof(event));
		event.ch = i;
		if (ioctl(dev_ctx.dev_fd, IFX_TAPI_EVENT_GET, &event)) {
			ast_mutex_unlock(&iflock);
			continue;
		}
		if (event.id == IFX_TAPI_EVENT_NONE) {
			ast_mutex_unlock(&iflock);
			continue;
		}

		ast_mutex_unlock(&iflock);

		switch(event.id) {
			case IFX_TAPI_EVENT_FXS_ONHOOK:
				lantiq_dev_event_hook(i, 1);
				break;
			case IFX_TAPI_EVENT_FXS_OFFHOOK:
				lantiq_dev_event_hook(i, 0);
				break;
			case IFX_TAPI_EVENT_DTMF_DIGIT:
				lantiq_dev_event_digit(i, (char)event.data.dtmf.ascii);
				break;
			case IFX_TAPI_EVENT_PULSE_DIGIT:
				if (event.data.pulse.digit == 0xB) {
					lantiq_dev_event_digit(i, '0');
				} else {
					lantiq_dev_event_digit(i, '0' + (char)event.data.pulse.digit);
				}
				break;
			case IFX_TAPI_EVENT_COD_DEC_CHG:
			case IFX_TAPI_EVENT_TONE_GEN_END:
			case IFX_TAPI_EVENT_CID_TX_SEQ_END:
				break;
			default:
				ast_log(LOG_ERROR, "Unknown TAPI event %08X. Restarting Asterisk...\n", event.id);
				sleep(1);
				ast_cli_command(-1, "core restart now");
				break;
		}
	}
}

static void * lantiq_events_monitor(void *data)
{
	ast_verbose("TAPI thread started\n");

	struct pollfd fds[TAPI_AUDIO_PORT_NUM_MAX + 1];
	int c;

	fds[0].fd = dev_ctx.dev_fd;
	fds[0].events = POLLIN;
	for (c = 0; c < dev_ctx.channels; c++) {
		fds[c + 1].fd = dev_ctx.ch_fd[c];
		fds[c + 1].events = POLLIN;
	}

	pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, NULL);
	for (;;) {
		if (poll(fds, dev_ctx.channels + 1, 2000) <= 0) {
			continue;
		}

		ast_mutex_lock(&monlock);
		if (fds[0].revents & POLLIN) {
			lantiq_dev_event_handler();
		}

		for (c = 0; c < dev_ctx.channels; c++) {
			if ((fds[c + 1].revents & POLLIN) && (lantiq_dev_data_handler(c))) {
				ast_log(LOG_ERROR, "data handler %d failed\n", c);
				break;
			}
		}
		ast_mutex_unlock(&monlock);
	}

	return NULL;
}

static int restart_monitor(void)
{
	/* If we're supposed to be stopped -- stay stopped */
	if (monitor_thread == AST_PTHREADT_STOP)
		return 0;

	ast_mutex_lock(&monlock);

	if (monitor_thread == pthread_self()) {
		ast_mutex_unlock(&monlock);
		ast_log(LOG_WARNING, "Cannot kill myself\n");
		return -1;
	}

	if (monitor_thread != AST_PTHREADT_NULL) {
		/* Wake up the thread */
		pthread_kill(monitor_thread, SIGURG);
	} else {
		/* Start a new monitor */
		if (ast_pthread_create_background(&monitor_thread, NULL, lantiq_events_monitor, NULL) < 0) {
			ast_mutex_unlock(&monlock);
			ast_log(LOG_ERROR, "Unable to start monitor thread.\n");
			return -1;
		}
	}
	ast_mutex_unlock(&monlock);

	return 0;
}

static void lantiq_cleanup(void)
{
	int c;

	if (dev_ctx.dev_fd < 0) {
		return;
	}

	for (c = 0; c < dev_ctx.channels ; c++) { 
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_STANDBY)) {
			ast_log(LOG_WARNING, "IFX_TAPI_LINE_FEED_SET ioctl failed\n");
		}

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_STOP, 0)) {
			ast_log(LOG_WARNING, "IFX_TAPI_ENC_STOP ioctl failed\n");
		}

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_DEC_STOP, 0)) {
			ast_log(LOG_WARNING, "IFX_TAPI_DEC_STOP ioctl failed\n");
		}
		led_off(dev_ctx.ch_led[c]);
	}

	if (ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_STOP, 0)) {
		ast_log(LOG_WARNING, "IFX_TAPI_DEV_STOP ioctl failed\n");
	}

	close(dev_ctx.dev_fd);
	dev_ctx.dev_fd = -1;
	led_off(dev_ctx.voip_led);
}

static int unload_module(void)
{
	int c;

	ast_channel_unregister(&lantiq_tech);

	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_WARNING, "Unable to lock the interface list\n");
		return -1;
	}
	for (c = 0; c < dev_ctx.channels ; c++) {
		if (iflist[c].owner)
			ast_softhangup(iflist[c].owner, AST_SOFTHANGUP_APPUNLOAD);
	}
	ast_mutex_unlock(&iflock);

	if (ast_mutex_lock(&monlock)) {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		return -1;
	}
	if (monitor_thread && (monitor_thread != AST_PTHREADT_STOP) && (monitor_thread != AST_PTHREADT_NULL)) {
		pthread_t th = monitor_thread;
		monitor_thread = AST_PTHREADT_STOP;
		pthread_cancel(th);
		pthread_kill(th, SIGURG);
		ast_mutex_unlock(&monlock);
		pthread_join(th, NULL);
	} else {
		monitor_thread = AST_PTHREADT_STOP;
		ast_mutex_unlock(&monlock);
	}

	sched_thread = ast_sched_thread_destroy(sched_thread);
	ast_mutex_destroy(&iflock);
	ast_mutex_destroy(&monlock);

	lantiq_cleanup();
	ast_free(iflist);

	return 0;
}

static struct lantiq_pvt *lantiq_init_pvt(struct lantiq_pvt *pvt)
{
	if (pvt) {
		pvt->owner = NULL;
		pvt->port_id = -1;
		pvt->channel_state = UNKNOWN;
		pvt->context[0] = '\0';
		pvt->ext[0] = '\0';
		pvt->dial_timer = 0;
		pvt->dtmfbuf[0] = '\0';
		pvt->dtmfbuf_len = 0;
		pvt->call_setup_start = 0;
		pvt->call_setup_delay = 0;
		pvt->call_answer = 0;
		pvt->jb_size = 0;
		pvt->jb_underflow = 0;
		pvt->jb_overflow = 0;
		pvt->jb_delay = 0;
		pvt->jb_invalid = 0;
	} else {
		ast_log(LOG_ERROR, "unable to clear pvt structure\n");
	}

	return pvt;
}

static int lantiq_create_pvts(void)
{
	int i;

	iflist = ast_calloc(1, sizeof(struct lantiq_pvt) * dev_ctx.channels);

	if (!iflist) {
		ast_log(LOG_ERROR, "unable to allocate memory\n");
		return -1;
	}

	for (i = 0; i < dev_ctx.channels; i++) {
		lantiq_init_pvt(&iflist[i]);
		iflist[i].port_id = i;
		if (per_channel_context) {
			snprintf(iflist[i].context, AST_MAX_CONTEXT, "%s%i", LANTIQ_CONTEXT_PREFIX, i + 1);
			ast_debug(1, "Context for channel %i: %s\n", i, iflist[i].context);
		} else {
			snprintf(iflist[i].context, AST_MAX_CONTEXT, "default");
		}
	}
	return 0;
}

static int lantiq_setup_rtp(int c)
{
	/* Configure RTP payload type tables */
	IFX_TAPI_PKT_RTP_PT_CFG_t rtpPTConf;

	memset((char*)&rtpPTConf, '\0', sizeof(rtpPTConf));

//	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_G723_63] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_G723_63] = AST_FORMAT_G723_1;
//	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_G723_53] = tpPTConf.nPTdown[IFX_TAPI_COD_TYPE_G723_53] = 4;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_G729] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_G729] = RTP_G729;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_MLAW] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_MLAW] = RTP_PCMU;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_ALAW] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_ALAW] = RTP_PCMA;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_G726_32] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_G726_32] = RTP_G726;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_ILBC_152] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_ILBC_152] = RTP_ILBC;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_LIN16_8] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_LIN16_8] = RTP_SLIN8;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_LIN16_16] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_LIN16_16] = RTP_SLIN16;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_G722_64] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_G722_64] = RTP_G722;
	rtpPTConf.nPTup[IFX_TAPI_COD_TYPE_G7221_32] = rtpPTConf.nPTdown[IFX_TAPI_COD_TYPE_G7221_32] = RTP_G7221;

	int ret;
	if ((ret = ioctl(dev_ctx.ch_fd[c], IFX_TAPI_PKT_RTP_PT_CFG_SET, (IFX_int32_t) &rtpPTConf))) {
		ast_log(LOG_ERROR, "IFX_TAPI_PKT_RTP_PT_CFG_SET failed: ret=%i\n", ret);
		return -1;
	}

	return 0;
}

static int load_module(void)
{
	struct ast_config *cfg;
	struct ast_variable *v;
	int txgain = 0;
	int rxgain = 0;
	int wlec_type = 0;
	int wlec_nlp = 0;
	int wlec_nbfe = 0;
	int wlec_nbne = 0;
	int wlec_wbne = 0;
	int jb_type = IFX_TAPI_JB_TYPE_ADAPTIVE;
	int jb_pckadpt = IFX_TAPI_JB_PKT_ADAPT_VOICE;
	int jb_localadpt = IFX_TAPI_JB_LOCAL_ADAPT_DEFAULT;
	int jb_scaling = 0x10;
	int jb_initialsize = 0x2d0;
	int jb_minsize = 0x50;
	int jb_maxsize = 0x5a0;
	int cid_type = IFX_TAPI_CID_STD_TELCORDIA;
	int vad_type = IFX_TAPI_ENC_VAD_NOVAD;
	dev_ctx.dev_fd = -1;
	dev_ctx.channels = TAPI_AUDIO_PORT_NUM_MAX;
	dev_ctx.interdigit_timeout = DEFAULT_INTERDIGIT_TIMEOUT;
	struct ast_flags config_flags = { 0 };
	int c;

	/* Turn off the LEDs, just in case */
	led_off(dev_ctx.voip_led);
	for(c = 0; c < TAPI_AUDIO_PORT_NUM_MAX; c++)
		led_off(dev_ctx.ch_led[c]);

	if ((cfg = ast_config_load(config, config_flags)) == CONFIG_STATUS_FILEINVALID) {
		ast_log(LOG_ERROR, "Config file %s is in an invalid format.  Aborting.\n", config);
		return AST_MODULE_LOAD_DECLINE;
	}

	/* We *must* have a config file otherwise stop immediately */
	if (!cfg) {
		ast_log(LOG_ERROR, "Unable to load config %s\n", config);
		return AST_MODULE_LOAD_DECLINE;
	}

	if (ast_mutex_lock(&iflock)) {
		ast_log(LOG_ERROR, "Unable to lock interface list.\n");
		goto cfg_error;
	}

	for (v = ast_variable_browse(cfg, "interfaces"); v; v = v->next) {
		if (!strcasecmp(v->name, "channels")) {
			dev_ctx.channels = atoi(v->value);
			if (!dev_ctx.channels) {
				ast_log(LOG_ERROR, "Invalid value for channels in config %s\n", config);
				goto cfg_error_il;
			}
		} else if (!strcasecmp(v->name, "firmwarefilename")) {
			ast_copy_string(firmware_filename, v->value, sizeof(firmware_filename));
		} else if (!strcasecmp(v->name, "bbdfilename")) {
			ast_copy_string(bbd_filename, v->value, sizeof(bbd_filename));
		} else if (!strcasecmp(v->name, "basepath")) {
			ast_copy_string(base_path, v->value, sizeof(base_path));
		} else if (!strcasecmp(v->name, "per_channel_context")) {
			if (!strcasecmp(v->value, "on")) {
				per_channel_context = 1;
			} else if (!strcasecmp(v->value, "off")) {
				per_channel_context = 0;
			} else {
				ast_log(LOG_ERROR, "Unknown per_channel_context value '%s'. Try 'on' or 'off'.\n", v->value);
				goto cfg_error_il;
			}
		}
	}

	for (v = ast_variable_browse(cfg, "general"); v; v = v->next) {
		if (!strcasecmp(v->name, "rxgain")) {
			rxgain = atoi(v->value);
			if (!rxgain) {
				rxgain = 0;
				ast_log(LOG_WARNING, "Invalid rxgain: %s, using default.\n", v->value);
			}
		} else if (!strcasecmp(v->name, "txgain")) {
			txgain = atoi(v->value);
			if (!txgain) {
				txgain = 0;
				ast_log(LOG_WARNING, "Invalid txgain: %s, using default.\n", v->value);
			}
		} else if (!strcasecmp(v->name, "echocancel")) {
			if (!strcasecmp(v->value, "off")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_OFF;
			} else if (!strcasecmp(v->value, "nlec")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_NE;
				if (!strcasecmp(v->name, "echocancelfixedwindowsize")) {
					wlec_nbne = atoi(v->value);
				}
			} else if (!strcasecmp(v->value, "wlec")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_NFE;
				if (!strcasecmp(v->name, "echocancelnfemovingwindowsize")) {
					wlec_nbfe = atoi(v->value);
				} else if (!strcasecmp(v->name, "echocancelfixedwindowsize")) {
					wlec_nbne = atoi(v->value);
				} else if (!strcasecmp(v->name, "echocancelwidefixedwindowsize")) {
					wlec_wbne = atoi(v->value);
				}
			} else if (!strcasecmp(v->value, "nees")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_NE_ES;
			} else if (!strcasecmp(v->value, "nfees")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_NFE_ES;
			} else if (!strcasecmp(v->value, "es")) {
				wlec_type = IFX_TAPI_WLEC_TYPE_ES;
			} else {
				wlec_type = IFX_TAPI_WLEC_TYPE_OFF;
				ast_log(LOG_ERROR, "Unknown echo cancellation type '%s'\n", v->value);
				goto cfg_error_il;
			}
		} else if (!strcasecmp(v->name, "echocancelnlp")) {
			if (!strcasecmp(v->value, "on")) {
				wlec_nlp = IFX_TAPI_WLEC_NLP_ON;
			} else if (!strcasecmp(v->value, "off")) {
				wlec_nlp = IFX_TAPI_WLEC_NLP_OFF;
			} else {
				ast_log(LOG_ERROR, "Unknown echo cancellation nlp '%s'\n", v->value);
				goto cfg_error_il;
			}
		} else if (!strcasecmp(v->name, "jitterbuffertype")) {
			if (!strcasecmp(v->value, "fixed")) {
				jb_type = IFX_TAPI_JB_TYPE_FIXED;
			} else if (!strcasecmp(v->value, "adaptive")) {
				jb_type = IFX_TAPI_JB_TYPE_ADAPTIVE;
				jb_localadpt = IFX_TAPI_JB_LOCAL_ADAPT_DEFAULT;
				if (!strcasecmp(v->name, "jitterbufferadaptation")) {
					if (!strcasecmp(v->value, "on")) {
						jb_localadpt = IFX_TAPI_JB_LOCAL_ADAPT_ON;
					} else if (!strcasecmp(v->value, "off")) {
						jb_localadpt = IFX_TAPI_JB_LOCAL_ADAPT_OFF;
					}
				} else if (!strcasecmp(v->name, "jitterbufferscalling")) {
					jb_scaling = atoi(v->value);
				} else if (!strcasecmp(v->name, "jitterbufferinitialsize")) {
					jb_initialsize = atoi(v->value);
				} else if (!strcasecmp(v->name, "jitterbufferminsize")) {
					jb_minsize = atoi(v->value);
				} else if (!strcasecmp(v->name, "jitterbuffermaxsize")) {
					jb_maxsize = atoi(v->value);
				}
			} else {
				ast_log(LOG_ERROR, "Unknown jitter buffer type '%s'\n", v->value);
				goto cfg_error_il;
			}
		} else if (!strcasecmp(v->name, "jitterbufferpackettype")) {
			if (!strcasecmp(v->value, "voice")) {
				jb_pckadpt = IFX_TAPI_JB_PKT_ADAPT_VOICE;
			} else if (!strcasecmp(v->value, "data")) {
				jb_pckadpt = IFX_TAPI_JB_PKT_ADAPT_DATA;
			} else if (!strcasecmp(v->value, "datanorep")) {
				jb_pckadpt = IFX_TAPI_JB_PKT_ADAPT_DATA_NO_REP;
			} else {
				ast_log(LOG_ERROR, "Unknown jitter buffer packet adaptation type '%s'\n", v->value);
				goto cfg_error_il;
			}
		} else if (!strcasecmp(v->name, "calleridtype")) {
			ast_log(LOG_DEBUG, "Setting CID type to %s.\n", v->value);
			if (!strcasecmp(v->value, "telecordia")) {
				cid_type = IFX_TAPI_CID_STD_TELCORDIA;
			} else if (!strcasecmp(v->value, "etsifsk")) {
				cid_type = IFX_TAPI_CID_STD_ETSI_FSK;
			} else if (!strcasecmp(v->value, "etsidtmf")) {
				cid_type = IFX_TAPI_CID_STD_ETSI_DTMF;
			} else if (!strcasecmp(v->value, "sin")) {
				cid_type = IFX_TAPI_CID_STD_SIN;
			} else if (!strcasecmp(v->value, "ntt")) {
				cid_type = IFX_TAPI_CID_STD_NTT;
			} else if (!strcasecmp(v->value, "kpndtmf")) {
				cid_type = IFX_TAPI_CID_STD_KPN_DTMF;
			} else if (!strcasecmp(v->value, "kpndtmffsk")) {
				cid_type = IFX_TAPI_CID_STD_KPN_DTMF_FSK;
			} else {
				ast_log(LOG_ERROR, "Unknown caller id type '%s'\n", v->value);
				goto cfg_error_il;
			}
		} else if (!strcasecmp(v->name, "voiceactivitydetection")) {
			if (!strcasecmp(v->value, "on")) {
				vad_type = IFX_TAPI_ENC_VAD_ON;
			} else if (!strcasecmp(v->value, "g711")) {
				vad_type = IFX_TAPI_ENC_VAD_G711;
			} else if (!strcasecmp(v->value, "cng")) {
				vad_type = IFX_TAPI_ENC_VAD_CNG_ONLY;
			} else if (!strcasecmp(v->value, "sc")) {
				vad_type = IFX_TAPI_ENC_VAD_SC_ONLY;
			} else {
				ast_log(LOG_ERROR, "Unknown voice activity detection value '%s'\n", v->value);
				goto cfg_error_il;
			}
		} else if (!strcasecmp(v->name, "interdigit")) {
			dev_ctx.interdigit_timeout = atoi(v->value);
			ast_log(LOG_DEBUG, "Setting interdigit timeout to %s.\n", v->value);
			if (!dev_ctx.interdigit_timeout) {
				dev_ctx.interdigit_timeout = DEFAULT_INTERDIGIT_TIMEOUT;
				ast_log(LOG_WARNING, "Invalid interdigit timeout: %s, using default.\n", v->value);
			}
		}
	}

	lantiq_create_pvts();

	ast_mutex_unlock(&iflock);
	ast_config_destroy(cfg);

	if (!(sched_thread = ast_sched_thread_create())) {
		ast_log(LOG_ERROR, "Unable to create scheduler thread\n");
		goto load_error;
	}

	if (ast_channel_register(&lantiq_tech)) {
		ast_log(LOG_ERROR, "Unable to register channel class 'Phone'\n");
		goto load_error_st;
	}
	
	/* tapi */
#ifdef TODO_TONES
	IFX_TAPI_TONE_t tone;
#endif
	IFX_TAPI_DEV_START_CFG_t dev_start;
	IFX_TAPI_MAP_DATA_t map_data;
	IFX_TAPI_LINE_VOLUME_t line_vol;
	IFX_TAPI_WLEC_CFG_t wlec_cfg;
	IFX_TAPI_JB_CFG_t jb_cfg;
	IFX_TAPI_CID_CFG_t cid_cfg;

	/* open device */
	dev_ctx.dev_fd = lantiq_dev_open(base_path, 0);

	if (dev_ctx.dev_fd < 0) {
		ast_log(LOG_ERROR, "lantiq TAPI device open function failed\n");
		goto load_error_st;
	}

	for (c = 0; c < dev_ctx.channels ; c++) {
		dev_ctx.ch_fd[c] = lantiq_dev_open(base_path, c + 1);

		if (dev_ctx.ch_fd[c] < 0) {
			ast_log(LOG_ERROR, "lantiq TAPI channel %d open function failed\n", c);
			goto load_error_st;
		}
	}

	if (lantiq_dev_firmware_download(dev_ctx.dev_fd, firmware_filename)) {
		ast_log(LOG_ERROR, "voice firmware download failed\n");
		goto load_error_st;
	}

	if (ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_STOP, 0)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEV_STOP ioctl failed\n");
		goto load_error_st;
	}

	memset(&dev_start, 0x0, sizeof(IFX_TAPI_DEV_START_CFG_t));
	dev_start.nMode = IFX_TAPI_INIT_MODE_VOICE_CODER;

	/* Start TAPI */
	if (ioctl(dev_ctx.dev_fd, IFX_TAPI_DEV_START, &dev_start)) {
		ast_log(LOG_ERROR, "IFX_TAPI_DEV_START ioctl failed\n");
		goto load_error_st;
	}

	for (c = 0; c < dev_ctx.channels ; c++) {
		/* tones */
#ifdef TODO_TONES
		memset(&tone, 0, sizeof(IFX_TAPI_TONE_t));
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_TONE_TABLE_CFG_SET, &tone)) {
			ast_log(LOG_ERROR, "IFX_TAPI_TONE_TABLE_CFG_SET %d failed\n", c);
			goto load_error_st;
		}
#endif
		/* ringing type */
		IFX_TAPI_RING_CFG_t ringingType;
		memset(&ringingType, 0, sizeof(IFX_TAPI_RING_CFG_t));
		ringingType.nMode = IFX_TAPI_RING_CFG_MODE_INTERNAL_BALANCED;
		ringingType.nSubmode = IFX_TAPI_RING_CFG_SUBMODE_DC_RNG_TRIP_FAST;
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_RING_CFG_SET, (IFX_int32_t) &ringingType)) {
			ast_log(LOG_ERROR, "IFX_TAPI_RING_CFG_SET failed\n");
			goto load_error_st;
		}

		/* ring cadence */
		IFX_char_t data[15] = { 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
								0x00, 0x00, 0x00, 0x00, 0x00,     
								0x00, 0x00, 0x00, 0x00, 0x00 };

		IFX_TAPI_RING_CADENCE_t ringCadence;
		memset(&ringCadence, 0, sizeof(IFX_TAPI_RING_CADENCE_t));
		memcpy(&ringCadence.data, data, sizeof(data));
		ringCadence.nr = sizeof(data) * 8;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_RING_CADENCE_HR_SET, &ringCadence)) {
			ast_log(LOG_ERROR, "IFX_TAPI_RING_CADENCE_HR_SET failed\n");
			goto load_error_st;
		}

		/* perform mapping */
		memset(&map_data, 0x0, sizeof(IFX_TAPI_MAP_DATA_t));
		map_data.nDstCh = c;
		map_data.nChType = IFX_TAPI_MAP_TYPE_PHONE;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_MAP_DATA_ADD, &map_data)) {
			ast_log(LOG_ERROR, "IFX_TAPI_MAP_DATA_ADD %d failed\n", c);
			goto load_error_st;
		}

		/* set line feed */
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_LINE_FEED_SET, IFX_TAPI_LINE_FEED_STANDBY)) {
			ast_log(LOG_ERROR, "IFX_TAPI_LINE_FEED_SET %d failed\n", c);
			goto load_error_st;
		}

		/* set volume */
		memset(&line_vol, 0, sizeof(line_vol));
		line_vol.nGainRx = rxgain;
		line_vol.nGainTx = txgain;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_PHONE_VOLUME_SET, &line_vol)) {
			ast_log(LOG_ERROR, "IFX_TAPI_PHONE_VOLUME_SET %d failed\n", c);
			goto load_error_st;
		}

		/* Configure line echo canceller */
		memset(&wlec_cfg, 0, sizeof(wlec_cfg));
		wlec_cfg.nType = wlec_type;
		wlec_cfg.bNlp = wlec_nlp;
		wlec_cfg.nNBFEwindow = wlec_nbfe;
		wlec_cfg.nNBNEwindow = wlec_nbne;
		wlec_cfg.nWBNEwindow = wlec_wbne;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_WLEC_PHONE_CFG_SET, &wlec_cfg)) {
			ast_log(LOG_ERROR, "IFX_TAPI_WLEC_PHONE_CFG_SET %d failed\n", c);
			goto load_error_st;
		}

		/* Configure jitter buffer */
		memset(&jb_cfg, 0, sizeof(jb_cfg));
		jb_cfg.nJbType = jb_type;
		jb_cfg.nPckAdpt = jb_pckadpt;
		jb_cfg.nLocalAdpt = jb_localadpt;
		jb_cfg.nScaling = jb_scaling;
		jb_cfg.nInitialSize = jb_initialsize;
		jb_cfg.nMinSize = jb_minsize;
		jb_cfg.nMaxSize = jb_maxsize;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_JB_CFG_SET, &jb_cfg)) {
			ast_log(LOG_ERROR, "IFX_TAPI_JB_CFG_SET %d failed\n", c);
			goto load_error_st;
		}

		/* Configure Caller ID type */
		memset(&cid_cfg, 0, sizeof(cid_cfg));
		cid_cfg.nStandard = cid_type;

		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_CID_CFG_SET, &cid_cfg)) {
			ast_log(LOG_ERROR, "IIFX_TAPI_CID_CFG_SET %d failed\n", c);
			goto load_error_st;
		}

		/* Configure voice activity detection */
		if (ioctl(dev_ctx.ch_fd[c], IFX_TAPI_ENC_VAD_CFG_SET, vad_type)) {
			ast_log(LOG_ERROR, "IFX_TAPI_ENC_VAD_CFG_SET %d failed\n", c);
			goto load_error_st;
		}

		/* Setup TAPI <-> internal RTP codec type mapping */
		if (lantiq_setup_rtp(c)) {
			goto load_error_st;
		}

		/* Set initial hook status */
		iflist[c].channel_state = lantiq_get_hookstatus(c);
		
		if (iflist[c].channel_state == UNKNOWN) {
			goto load_error_st;
		}
	}

	/* make sure our device will be closed properly */
	ast_register_atexit(lantiq_cleanup);

	restart_monitor();
	led_on(dev_ctx.voip_led);
	return AST_MODULE_LOAD_SUCCESS;

cfg_error_il:
	ast_mutex_unlock(&iflock);
cfg_error:
	ast_config_destroy(cfg);
	return AST_MODULE_LOAD_DECLINE;

load_error_st:
	sched_thread = ast_sched_thread_destroy(sched_thread);
load_error:
	unload_module();
	ast_free(iflist);
	return AST_MODULE_LOAD_FAILURE;
}

AST_MODULE_INFO(ASTERISK_GPL_KEY, AST_MODFLAG_LOAD_ORDER, "Lantiq TAPI Telephony API Support",
	.load = load_module,
	.unload = unload_module,
	.load_pri = AST_MODPRI_CHANNEL_DRIVER
);
