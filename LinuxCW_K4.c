/*
 *  LinuxCW K4 morse code trainer v1.15.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sched.h>
#include <unistd.h>
#include <signal.h>
#include <fcntl.h>
#include <errno.h>
#include <getopt.h>
#include <alsa/asoundlib.h>
#include <sys/time.h>
#include <math.h>
#include <linux/input.h>
#include <pthread.h>

#define INPUT_NODISP "stty -echo"
#define INPUT_NORMAL "stty echo"
#define MIN_TIME_DA 160000
#define MAX_TIME_VAL 200000
#define MAX_TIME_SPACE 500000

#define INPUT_KEYBOARD "/dev/input/event"

int EVENTnum = 3, usec_DI = 80000, usec_DA = 250000, usec_SGap = 50000, usec_BGap = 320000;

const char* const TriMorse = "?ET?IA?NM????SU?RW????DK?GO?????????????HV?F?????L??PJ?????????????BX?CY????ZQ";
const char* const PntaCode = "09?8???7?????/?61???????2???3?45";
const char* const HexaCode = "????????????,?????()!;???????????'???@????.???????_????????????\n\0";

static char *device = "default";         /* playback device */
static snd_pcm_format_t format = SND_PCM_FORMAT_S16;    /* sample format */
static unsigned int rate = 44100;           /* stream rate */
static unsigned int channels = 1;           /* count of channels */
static unsigned int buffer_time = 5000;       /* ring buffer length in us */
static unsigned int period_time = 1000;       /* period time in us */
static double freq = 750;               /* tone frequency in Hz */
static int resample = 1;                /* enable alsa-lib resampling */
static int period_event = 0;                /* produce poll event after each period */
volatile int OnWav = 0;
volatile int m_Interrupt = 0;
static int KeyEventAccess = 0;
static int TriNum = 0, BinNum = 0, WordLen = 0;
static snd_pcm_sframes_t buffer_size;
static snd_pcm_sframes_t period_size;
static snd_output_t *output = NULL;
struct timeval keyUp_time, keyDown_time, current_time;
pthread_mutex_t mutex;
void * ReadFile_AK();
char filename[64];

static void generate_sine(const snd_pcm_channel_area_t *areas, 
              snd_pcm_uframes_t offset,
              int count, double *_phase)
{
    static double max_phase = 2. * M_PI;
    double phase = *_phase;
    double step = max_phase*freq/(double)rate;
    unsigned char *samples[channels];
    int steps[channels];
    unsigned int chn;
    int format_bits = snd_pcm_format_width(format);
    unsigned int maxval = (1 << (format_bits - 1)) - 1;
    int bps = format_bits / 8;  /* bytes per sample */
    int phys_bps = snd_pcm_format_physical_width(format) / 8;
    int big_endian = snd_pcm_format_big_endian(format) == 1;
    int to_unsigned = snd_pcm_format_unsigned(format) == 1;
    int is_float = (format == SND_PCM_FORMAT_FLOAT_LE ||
            format == SND_PCM_FORMAT_FLOAT_BE);
    /* verify and prepare the contents of areas */
    for (chn = 0; chn < channels; chn++) {
        if ((areas[chn].first % 8) != 0) {
            printf("areas[%u].first == %u, aborting...\n", chn, areas[chn].first);
            exit(EXIT_FAILURE);
        }
        samples[chn] = /*(signed short *)*/(((unsigned char *)areas[chn].addr) + (areas[chn].first / 8));
        if ((areas[chn].step % 16) != 0) {
            printf("areas[%u].step == %u, aborting...\n", chn, areas[chn].step);
            exit(EXIT_FAILURE);
        }
        steps[chn] = areas[chn].step / 8;
        samples[chn] += offset * steps[chn];
    }
    /* fill the channel areas */
    while (count-- > 0) {
        union {
            float f;
            int i;
        } fval;
        int res, i;
        if (is_float) {
            fval.f = sin(phase);
            res = fval.i;
        } else
            res = sin(phase) * maxval;
        if (to_unsigned)
            res ^= 1U << (format_bits - 1);
        for (chn = 0; chn < channels; chn++) {
            /* Generate data in native endian format */
            if (big_endian) {
                for (i = 0; i < bps; i++)
                    *(samples[chn] + phys_bps - 1 - i) = (res >> i * 8) & 0xff;
            } else {
                for (i = 0; i < bps; i++)
                    *(samples[chn] + i) = (res >>  i * 8) & 0xff;
            }
            samples[chn] += steps[chn];
        }
        phase += step;
        if (phase >= max_phase)
            phase -= max_phase;
    }
    *_phase = phase;
}
static int set_hwparams(snd_pcm_t *handle,
            snd_pcm_hw_params_t *params,
            snd_pcm_access_t access)
{
    unsigned int rrate;
    snd_pcm_uframes_t size;
    int err, dir;
    /* choose all parameters */
    if ((err = snd_pcm_hw_params_any(handle, params)) < 0) {
        printf("[!] Broken configuration for playback: no configurations available: %s\n", snd_strerror(err));
        return err;
    }
    /* set hardware resampling */
    if ((err = snd_pcm_hw_params_set_rate_resample(handle, params, resample)) < 0) {
        printf("[!] Resampling setup failed for playback: %s\n", snd_strerror(err));
        return err;
    }
    /* set the interleaved read/write format */
    if ((err = snd_pcm_hw_params_set_access(handle, params, access)) < 0) {
        printf("[!] Access type not available for playback: %s\n", snd_strerror(err));
        return err;
    }
    /* set the sample format */
    if ((err = snd_pcm_hw_params_set_format(handle, params, format)) < 0) {
        printf("[!] Sample format not available for playback: %s\n", snd_strerror(err));
        return err;
    }
    /* set the count of channels */
    if ((err = snd_pcm_hw_params_set_channels(handle, params, channels)) < 0) {
        printf("[!] Channels count (%u) not available for playbacks: %s\n", channels, snd_strerror(err));
        return err;
    }
    /* set the stream rate */
    rrate = rate;
    if ((err = snd_pcm_hw_params_set_rate_near(handle, params, &rrate, 0)) < 0) {
        printf("[!] Rate %uHz not available for playback: %s\n", rate, snd_strerror(err));
        return err;
    }
    if (rrate != rate) {
        printf("[!] Rate doesn't match (requested %uHz, get %iHz)\n", rate, err);
        return -EINVAL;
    }
    /* set the buffer time */
    if ((err = snd_pcm_hw_params_set_buffer_time_near(handle, params, &buffer_time, &dir)) < 0) {
        printf("[!] Unable to set buffer time %u for playback: %s\n", buffer_time, snd_strerror(err));
        return err;
    }
    if ((err = snd_pcm_hw_params_get_buffer_size(params, &size)) < 0) {
        printf("[!] Unable to get buffer size for playback: %s\n", snd_strerror(err));
        return err;
    }
    buffer_size = size;
    /* set the period time */
    if ((err = snd_pcm_hw_params_set_period_time_near(handle, params, &period_time, &dir)) < 0) {
        printf("[!] Unable to set period time %u for playback: %s\n", period_time, snd_strerror(err));
        return err;
    }
    if ((err = snd_pcm_hw_params_get_period_size(params, &size, &dir)) < 0) {
        printf("[!] Unable to get period size for playback: %s\n", snd_strerror(err));
        return err;
    }
    period_size = size;
    /* write the parameters to device */
    if ((err = snd_pcm_hw_params(handle, params)) < 0) {
        printf("[!] Unable to set hw params for playback: %s\n", snd_strerror(err));
        return err;
    }
    return 0;
}
static int set_swparams(snd_pcm_t *handle, snd_pcm_sw_params_t *swparams)
{
    int err;
    /* get the current swparams */
    if ((err = snd_pcm_sw_params_current(handle, swparams)) < 0) {
        printf("[!] Unable to determine current swparams for playback: %s\n", snd_strerror(err));
        return err;
    }
    /* start the transfer when the buffer is almost full: */
    /* (buffer_size / avail_min) * avail_min */
    if ((err = snd_pcm_sw_params_set_start_threshold(handle, swparams, (buffer_size / period_size) * period_size)) < 0) {
        printf("[!] Unable to set start threshold mode for playback: %s\n", snd_strerror(err));
        return err;
    }
    /* allow the transfer when at least period_size samples can be processed */
    /* or disable this mechanism when period event is enabled (aka interrupt like style processing) */
    if ((err = snd_pcm_sw_params_set_avail_min(handle, swparams, period_event ? buffer_size : period_size)) < 0) {
        printf("[!] Unable to set avail min for playback: %s\n", snd_strerror(err));
        return err;
    }
    /* enable period events when requested */
    if (period_event) {
        if ((err = snd_pcm_sw_params_set_period_event(handle, swparams, 1)) < 0) {
            printf("[!] Unable to set period event: %s\n", snd_strerror(err));
            return err;
        }
    }
    /* write the parameters to the playback device */
    if ((err = snd_pcm_sw_params(handle, swparams)) < 0) {
        printf("[!] Unable to set sw params for playback: %s\n", snd_strerror(err));
        return err;
    }
    return 0;
}
/*
 *   Underrun and suspend recovery
 */
 
static int xrun_recovery(snd_pcm_t *handle, int err)
{
    if (err == -EPIPE) {    /* under-run */
        err = snd_pcm_prepare(handle);
        if (err < 0)
            printf("[!] Can't recovery from underrun, prepare failed: %s\n", snd_strerror(err));
        return 0;
    } else if (err == -ESTRPIPE) {
        while ((err = snd_pcm_resume(handle)) == -EAGAIN)
            sleep(1);   /* wait until the suspend flag is released */
        if (err < 0) {
            err = snd_pcm_prepare(handle);
            if (err < 0)
                printf("[!] Can't recovery from suspend, prepare failed: %s\n", snd_strerror(err));
        }
        return 0;
    }
    return err;
}
/*
 *   Transfer method - write only
 */
static int write_loop(snd_pcm_t *handle,
              signed short *samples,
              snd_pcm_channel_area_t *areas)
{
    double phase = 0;
    signed short *ptr;
    int err, cptr;
    while (!m_Interrupt){
      while (OnWav){
        generate_sine(areas, 0, period_size, &phase);
        ptr = samples;
        cptr = period_size;
        while (cptr > 0) {
            err = snd_pcm_writei(handle, ptr, cptr);
            if (err == -EAGAIN)
                continue;
            if (err < 0) {
                if (xrun_recovery(handle, err) < 0) {
                    printf("[!] Write error: %s\n", snd_strerror(err));
                    return -1;
                }
                break;  /* skip one period */
            }
            ptr += err * channels;
            cptr -= err;
        }
      }
    }printf("\n=============================\n");
    return 0;
}

static int write_from_file(snd_pcm_t *handle,
              signed short *samples,
              snd_pcm_channel_area_t *areas)
{
    int rf;
    pthread_t RF_pid;
    OnWav = 0;m_Interrupt = 0;
    if((rf = pthread_create(&RF_pid, NULL, ReadFile_AK, NULL))<0){
        printf("[!] Fail to create AutoKey thread.\n");
    }
    write_loop(handle,samples,areas);
    pthread_join(RF_pid,NULL);printf("[-] AutoKey closed.\n");
    OnWav = 0;m_Interrupt = 0;
    return 0;
}

struct transfer_method {
    const char *name;
    snd_pcm_access_t access;
    int (*transfer_loop)(snd_pcm_t *handle,
                 signed short *samples,
                 snd_pcm_channel_area_t *areas);
};
static struct transfer_method transfer_methods[] = {
    { "write", SND_PCM_ACCESS_RW_INTERLEAVED, write_loop },
    { "write", SND_PCM_ACCESS_RW_INTERLEAVED, write_from_file },
    { NULL, SND_PCM_ACCESS_RW_INTERLEAVED, NULL }
};

int PressKey(int usec)
{
   OnWav=1;usleep(usec);OnWav=0;
   return 0;
}

void * ReadFile_AK()
{
    FILE *fin;
    char letter;
    if((fin=fopen(filename,"r"))==NULL){
        printf("Unable to read file.\n");return 0;
    }
    while((letter=fgetc(fin))!=EOF){
      switch(letter){
      case 'A':
      case 'a':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);
        putchar('A');usleep(usec_BGap);
        break;
      case 'B':
      case 'b':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar('B');usleep(usec_BGap);
        break;
      case 'C':
      case 'c':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);
        putchar('C');usleep(usec_BGap);
        break;
      case 'D':
      case 'd':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar('D');usleep(usec_BGap);
        break;
      case 'E':
      case 'e':
        PressKey(usec_DI);
        putchar('E');usleep(usec_BGap);
        break;
      case 'F':
      case 'f':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);
        putchar('F');usleep(usec_BGap);
        break;
      case 'G':
      case 'g':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);
        putchar('G');usleep(usec_BGap);
        break;
      case 'H':
      case 'h':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar('H');usleep(usec_BGap);
        break;
      case 'I':
      case 'i':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar('I');usleep(usec_BGap);
        break;
      case 'J':
      case 'j':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar('J');usleep(usec_BGap);
        break;
      case 'K':
      case 'k':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);
        putchar('K');usleep(usec_BGap);
        break;
      case 'L':
      case 'l':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar('L');usleep(usec_BGap);
        break;
      case 'M':
      case 'm':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar('M');usleep(usec_BGap);
        break;
      case 'N':
      case 'n':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);
        putchar('N');usleep(usec_BGap);
        break;
      case 'O':
      case 'o':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar('O');usleep(usec_BGap);
        break;
      case 'P':
      case 'p':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);
        putchar('P');usleep(usec_BGap);
        break;
      case 'Q':
      case 'q':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);
        putchar('Q');usleep(usec_BGap);
        break;
      case 'R':
      case 'r':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);
        putchar('R');usleep(usec_BGap);
        break;
      case 'S':
      case 's':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar('S');usleep(usec_BGap);
        break;
      case 'T':
      case 't':
        PressKey(usec_DA);
        putchar('T');usleep(usec_BGap);
        break;
      case 'U':
      case 'u':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);
        putchar('U');usleep(usec_BGap);
        break;
      case 'V':
      case 'v':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);
        putchar('V');usleep(usec_BGap);
        break;
      case 'W':
      case 'w':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar('W');usleep(usec_BGap);
        break;
      case 'X':
      case 'x':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);
        putchar('X');usleep(usec_BGap);
        break;
      case 'Y':
      case 'y':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar('Y');usleep(usec_BGap);
        break;
      case 'Z':
      case 'z':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar('Z');usleep(usec_BGap);
        break;
      case '0':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar(letter);usleep(usec_BGap);
        break;
      case '1':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar(letter);usleep(usec_BGap);
        break;
      case '2':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar(letter);usleep(usec_BGap);
        break;
      case '3':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar(letter);usleep(usec_BGap);
        break;
      case '4':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);
        putchar(letter);usleep(usec_BGap);
        break;
      case '5':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar(letter);usleep(usec_BGap);
        break;
      case '6':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar(letter);usleep(usec_BGap);
        break;
      case '7':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar(letter);usleep(usec_BGap);
        break;
      case '8':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar(letter);usleep(usec_BGap);
        break;
      case '9':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);
        putchar(letter);usleep(usec_BGap);
        break;
      case '/':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);
        putchar(letter);usleep(usec_BGap);
        break;
      case ',':
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);
        PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);
        putchar(letter);usleep(usec_BGap);
        break;
      case '?':
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);PressKey(usec_DA);usleep(usec_SGap);
        PressKey(usec_DI);usleep(usec_SGap);PressKey(usec_DI);
        putchar(letter);usleep(usec_BGap);
        break;
      default:
        putchar(letter);
        usleep(usec_BGap);
        break;
      }
    }
    m_Interrupt=1;OnWav=0;
    fclose(fin);
    return 0;
}

void * KeyDaemon_CW()
{
    char access_KB[32], full_INPUT[64];
    int fd = -1, ret = -1;
    struct input_event ev;
    sprintf(full_INPUT,"%s%d",INPUT_KEYBOARD,EVENTnum);
    if((fd = open(full_INPUT, O_RDONLY)) < 0) {
        sprintf(access_KB,"%s%s","sudo chmod +r ",full_INPUT);
        printf("LinuxCW needs sudo to access your keyboard input.\n");
        system(access_KB);
        if((fd = open(full_INPUT, O_RDONLY)) < 0) {
        printf("[!] cannot access keyboard, error:%d\n", errno);
        return 0;}
        printf("Validated!\n");
    }
    KeyEventAccess = 1;
    sleep(1);
    while(1) {
        memset(&ev, 0, sizeof(struct input_event));

        ret = read(fd, &ev, sizeof(struct input_event));
        if (ret != sizeof(struct input_event)) {
            printf("read error, ret: %d\n", ret);
            break;
        }
        pthread_mutex_lock(&mutex);
        if (ev.type == EV_KEY) {
            if(!OnWav && (ev.code!=0x1C) && (ev.code!=0x01)){OnWav = 1;gettimeofday(&keyUp_time,NULL);}
            if(ev.value == 0 && OnWav){                
                OnWav = 0;
                WordLen++;
                TriNum*=3;
                BinNum*=2;
                gettimeofday(&keyDown_time,NULL);
                if(1000000*(keyDown_time.tv_sec-keyUp_time.tv_sec)+(keyDown_time.tv_usec-keyUp_time.tv_usec)<MIN_TIME_DA){
                    TriNum+=1;
                    BinNum++;
                }else{
                    TriNum+=2;
                }
            }
        }
        pthread_mutex_unlock(&mutex);
    }
    close(fd);
    return 0;
}

void * PrintDaemon()
{
    long AFK_time;
    int AFK_level = 1, Bracket = 0;
    while(!m_Interrupt){
        pthread_mutex_lock(&mutex);
        AFK_level=WordLen?0:AFK_level;
        if(!OnWav && !AFK_level){
            gettimeofday(&current_time,NULL);
            AFK_time = 1000000*(current_time.tv_sec-keyDown_time.tv_sec)+(current_time.tv_usec-keyDown_time.tv_usec);
            if(WordLen && AFK_time>MAX_TIME_VAL){
                if(WordLen<5){
                    putchar(TriMorse[TriNum]);
                }else if(WordLen==5){
                    putchar(PntaCode[BinNum]);
                }else if(WordLen==6){
                    if(BinNum==18){
                        putchar(HexaCode[BinNum+Bracket]);
                        Bracket=(Bracket==0)?1:0;
                    }else{
                        putchar(HexaCode[BinNum]);
                    }
                }else{
                    printf(" correction-> ");
                }
                WordLen=0;TriNum=0;BinNum=0;
            }
            if(AFK_time>MAX_TIME_SPACE){
                putchar(' ');AFK_level=1;
            }
        }
        pthread_mutex_unlock(&mutex);
        usleep(5000);
    }
    return 0;
}

int SoundDaemon_mod(int method)
{    
    snd_pcm_t *handle;
    int err;
    snd_pcm_hw_params_t *hwparams;
    snd_pcm_sw_params_t *swparams;
    signed short *samples;
    unsigned int chn;
    snd_pcm_channel_area_t *areas;
    snd_pcm_hw_params_alloca(&hwparams);
    snd_pcm_sw_params_alloca(&swparams);
    
    if ((err = snd_output_stdio_attach(&output, stdout, 0)) < 0) {
        printf("[!] Output failed: %s\n", snd_strerror(err));
        return -1;
    }
    if ((err = snd_pcm_open(&handle, device, SND_PCM_STREAM_PLAYBACK, 0)) < 0) {
        printf("[!] Playback open error: %s\n", snd_strerror(err));
        return -1;
    }
    
    if ((err = set_hwparams(handle, hwparams, transfer_methods[method].access)) < 0) {
        printf("[!] Setting of hwparams failed: %s\n", snd_strerror(err));
        return -1;
    }
    if ((err = set_swparams(handle, swparams)) < 0) {
        printf("[!] Setting of swparams failed: %s\n", snd_strerror(err));
        return -1;
    }
    samples = malloc((period_size * channels * snd_pcm_format_physical_width(format)) / 8);
    if (samples == NULL) {
        printf("[!] No enough memory. Error code: samples\n");
        return -1;
    }
    if ((areas = calloc(channels, sizeof(snd_pcm_channel_area_t))) == NULL) {
        printf("[!] No enough memory. Error code: areas\n");
        return -1;
    }
    for (chn = 0; chn < channels; chn++) {
        areas[chn].addr = samples;
        areas[chn].first = chn * snd_pcm_format_physical_width(format);
        areas[chn].step = channels * snd_pcm_format_physical_width(format);
    }
    err = transfer_methods[method].transfer_loop(handle, samples, areas);
    if (err < 0){
        printf("[!] Transfer failed: %s\n", snd_strerror(err));
    }
    free(areas);
    free(samples);
    snd_pcm_close(handle);printf("[-] SoundDaemon closed.\n");
    return 0;
}

void * getEnter()
{
    //inspect key value
    while(1){
        switch (getchar())
        {
            case 3:
              pthread_mutex_lock(&mutex);OnWav = 0;m_Interrupt = 1;pthread_mutex_unlock(&mutex);printf("[!] Manually interrupted by Ctrl-C.\n");return 0;
            case 0x1B:
              pthread_mutex_lock(&mutex);OnWav = 0;m_Interrupt = 1;pthread_mutex_unlock(&mutex);return 0;
            case '\n':
              putchar('\n');break;
        }
    }
    return 0;
}

int main(int argc, char *argv[])
{
    setbuf(stdout,NULL);
    struct option long_option[] =
    {
        {"help", 0, NULL, 'h'},
        {"event", 1, NULL, 'e'},
        {"rate", 1, NULL, 'r'},
        {"frequency", 1, NULL, 'f'},
        {"input", 1, NULL, 'i'},
        {NULL, 0, NULL, 0}
    };

    int rc, rp, rb, rs, countpf, Copt;
    pthread_t CW_pid, SC_pid, BL_pid;

    while (1) {
        if ((Copt = getopt_long(argc, argv, "he:r:f:i:", long_option, NULL)) < 0)
            break;
        switch (Copt) {
        case 'h':
            printf("Usage: %s [-option] [args]...\n",argv[0]);
            return 0;
        case 'e':
            EVENTnum = atoi(optarg);
            EVENTnum < 0 ? 0 : EVENTnum;
            break;
        case 'r':
            rate = atoi(optarg);
            rate = rate < 4000 ? 4000 : rate;
            rate = rate > 196000 ? 196000 : rate;
            break;
        case 'f':
            freq = atoi(optarg);
            freq = freq < 250 ? 250 : freq;
            freq = freq > 1000 ? 1000 : freq;
            break;
        case 'i':
            sprintf(filename,"%s",optarg);
            SoundDaemon_mod(1);
            return 0;
        }
    }


    pthread_mutex_init(&mutex,NULL);//initiate lock for global interchange.

    for(countpf=3;countpf>0;countpf--){printf("Record will start in %d sec, please get ready...\n",countpf);sleep(1);}

    system(INPUT_NODISP);


    if((rc = pthread_create(&CW_pid, NULL, KeyDaemon_CW, NULL))<0){
        printf("[!] Fail to create KeyDaemon thread.\n");
    }
    while(!KeyEventAccess){sleep(0.5);}
    if((rp = pthread_create(&SC_pid, NULL, PrintDaemon, NULL))<0){
        printf("[!] Fail to create PrintDaemon thread.\n");
    }
    if((rb = pthread_create(&BL_pid, NULL, getEnter, NULL))<0){
        printf("[!] Fail to create KeyBlocker thread.\n");
    }else{
        printf("\n[+] KeyBlocker is on (press ENTER to start a new line)\n\nAll can be interrupted by ESC-ENTER.\n\nYour scripts:\n\n");
    }
    if((rs = SoundDaemon_mod(0))<0){
        printf("[!] SoundDaemon quit with errors.\n");
    }
    system(INPUT_NORMAL);
    pthread_join(SC_pid,NULL);printf("[-] PrintDaemon closed.\n");
    pthread_join(BL_pid,NULL);printf("[-] KeyBlocker closed.\n");
    pthread_mutex_destroy(&mutex);
    return 0;
}
