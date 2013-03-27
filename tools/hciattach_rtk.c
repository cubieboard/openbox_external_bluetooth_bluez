/**
Copyright @ Realtek Semiconductor Corp. All Rights Reserved.

Module Name:
	hciattach_rtk.c

Description:
	H4/H5 specific initialization

Revision History:
	   When                 Who                               What
	----------         ---------------            -------------------------------
	2011-12-14 	   andy_xu@realsil.com.cn                  Create.
	2011-12-20	   evan_bao@realsil.com.cn                 Modify.

--*/

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <stdlib.h>
#include <termios.h>
#include <time.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/param.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <signal.h>
#include <bluetooth/bluetooth.h>
#include <bluetooth/hci.h>
#include <bluetooth/hci_lib.h>

#include "hciattach.h"

typedef unsigned char		RT_U8,   *PRT_U8;
typedef unsigned short		RT_U16,  *PRT_U16;
typedef signed long		RT_S32,  *PRT_S32;
typedef unsigned long           RT_U32,  *PRT_U32;      //long is 32 bit,K.C
typedef signed char             RT_S8,   *PRT_S8;

struct sk_buff
{
    RT_U32 max_len; 
    RT_U32 data_len;
    RT_U8  data[1];
};


/* Skb helpers */
struct bt_skb_cb 
{
    RT_U8 pkt_type;
    RT_U8 incoming;
    RT_U16 expect;
    RT_U8 tx_seq;
    RT_U8 retries;
    RT_U8 sar;
    unsigned short channel;
};

typedef struct {
	uint8_t		index;
	uint8_t		data[252];
} __attribute__ ((packed)) download_vendor_patch_cp;

#define bt_cb(skb) ((struct bt_skb_cb *)((skb)->cb))
#if 0
#define RS_DBG(fmt, arg...) printf(fmt "\n" , ##arg)
#else
#define RS_DBG(fmt, arg...)
#endif

#define FIRMWARE_DIRECTORY "/system/vendor/modules/"
#define BT_CONFIG_DIRECTORY "/system/vendor/modules/"
#define PATCH_DATA_FIELD_MAX_SIZE     252
#define READ_DATA_SIZE  							32


// HCI data types //
#define BCSP_ACK_PKT	        0x00
#define HCI_COMMAND_PKT         0x01
#define HCI_ACLDATA_PKT         0x02
#define HCI_SCODATA_PKT         0x03
#define HCI_EVENT_PKT           0x04
#define H5_VDRSPEC_PKT	        0x0E
#define BCSP_LINK_CTL_PKT       0x0F
#define BCSP_LE_PKT	        0x0F


#pragma pack(1)
#if __BYTE_ORDER == __LITTLE_ENDIAN
typedef struct _BCSP_PKT_HEADER
{
    RT_U8 SeqNumber:3;
    RT_U8 AckNumber:3;
    RT_U8 DicPresent:1; // Data Integrity Check Present
    RT_U8 ReliablePkt:1;

    RT_U16 PktType:4;
    RT_U16 PayloadLen:12;

    RT_U8 HdrChecksum;
}BCSP_PKT_HEADER;
#else
typedef struct _BCSP_PKT_HEADER
{
    RT_U8 ReliablePkt:1;
    RT_U8 DicPresent:1; // Data Integrity Check Present
    RT_U8 AckNumber:3;
    RT_U8 SeqNumber:3;

    RT_U16 PayloadLen:12;
    RT_U16 PktType:4;

    RT_U8 HdrChecksum;
}BCSP_PKT_HEADER;
#endif

typedef enum _BCSP_RX_STATE
{
    BCSP_W4_PKT_DELIMITER,
    BCSP_W4_PKT_START,
    BCSP_W4_BCSP_HDR,
    BCSP_W4_DATA,
    BCSP_W4_CRC
} BCSP_RX_STATE;

typedef enum _BCSP_RX_ESC_STATE
{
    BCSP_ESCSTATE_NOESC,
    BCSP_ESCSTATE_ESC
} BCSP_RX_ESC_STATE;

typedef enum _BCSP_LINK_STATE
{
    BCSP_H5_SYNC,
    BCSP_H5_CONFIG,
	BCSP_H5_INIT,
    BCSP_H5_PATCH,
    BCSP_H5_ACTIVE
} BCSP_LINK_STATE;

typedef enum _PATCH_PROTOCOL
{
    PATCH_PROTOCAL_H4,
    PATCH_PROTOCAL_H5
} PATCH_PROTOCOL;

static int serial_fd;
static int bcsp_max_retries = 10;

struct bcsp_struct {
//    LIST_ENTRY unack;	// Unack'ed packets queue /
//    LIST_ENTRY rel;	    // Reliable packets queue //
//    LIST_ENTRY unrel;	// Unreliable packets queue //

    RT_U8	rxseq_txack;		// rxseq == txack. // expected rx SeqNumber
    RT_U8	rxack;			// Last packet sent by us that the peer ack'ed //
//    LIST_ENTRY tbcsp;

    RT_U8	use_crc;
    RT_U8	is_txack_req;		// txack required? Do we need to send ack's to the peer? //

    // Reliable packet sequence number - used to assign seq to each rel pkt. */
    RT_U8	msgq_txseq;		//next pkt seq 

    RT_U16	message_crc;
    RT_U32	rx_count;  		//expected pkts to recv

    BCSP_RX_STATE rx_state;
    BCSP_RX_ESC_STATE rx_esc_state;
    BCSP_LINK_STATE link_estab_state;

    struct	sk_buff *rx_skb;
	struct sk_buff* host_last_cmd;
};
static struct bcsp_struct rtk_bcsp;

//static int guse_init_uart_rate = 1; //this value is to decide whether use new setting uart value

struct patch_struct {
    int		nTxIndex; 	// current sending pkt number
    int 	nTotal; 	// total pkt number
    int		nRxIndex; 	// ack index from board
    int		nNeedRetry;	// if no response from board 
};
static struct patch_struct rtk_patch;

// bite reverse in bytes
// 00000001 -> 10000000
// 00000100 -> 00100000
const RT_U8 byte_rev_table[256] = {
    0x00, 0x80, 0x40, 0xc0, 0x20, 0xa0, 0x60, 0xe0,
    0x10, 0x90, 0x50, 0xd0, 0x30, 0xb0, 0x70, 0xf0,
    0x08, 0x88, 0x48, 0xc8, 0x28, 0xa8, 0x68, 0xe8,
    0x18, 0x98, 0x58, 0xd8, 0x38, 0xb8, 0x78, 0xf8,
    0x04, 0x84, 0x44, 0xc4, 0x24, 0xa4, 0x64, 0xe4,
    0x14, 0x94, 0x54, 0xd4, 0x34, 0xb4, 0x74, 0xf4,
    0x0c, 0x8c, 0x4c, 0xcc, 0x2c, 0xac, 0x6c, 0xec,
    0x1c, 0x9c, 0x5c, 0xdc, 0x3c, 0xbc, 0x7c, 0xfc,
    0x02, 0x82, 0x42, 0xc2, 0x22, 0xa2, 0x62, 0xe2,
    0x12, 0x92, 0x52, 0xd2, 0x32, 0xb2, 0x72, 0xf2,
    0x0a, 0x8a, 0x4a, 0xca, 0x2a, 0xaa, 0x6a, 0xea,
    0x1a, 0x9a, 0x5a, 0xda, 0x3a, 0xba, 0x7a, 0xfa,
    0x06, 0x86, 0x46, 0xc6, 0x26, 0xa6, 0x66, 0xe6,
    0x16, 0x96, 0x56, 0xd6, 0x36, 0xb6, 0x76, 0xf6,
    0x0e, 0x8e, 0x4e, 0xce, 0x2e, 0xae, 0x6e, 0xee,
    0x1e, 0x9e, 0x5e, 0xde, 0x3e, 0xbe, 0x7e, 0xfe,
    0x01, 0x81, 0x41, 0xc1, 0x21, 0xa1, 0x61, 0xe1,
    0x11, 0x91, 0x51, 0xd1, 0x31, 0xb1, 0x71, 0xf1,
    0x09, 0x89, 0x49, 0xc9, 0x29, 0xa9, 0x69, 0xe9,
    0x19, 0x99, 0x59, 0xd9, 0x39, 0xb9, 0x79, 0xf9,
    0x05, 0x85, 0x45, 0xc5, 0x25, 0xa5, 0x65, 0xe5,
    0x15, 0x95, 0x55, 0xd5, 0x35, 0xb5, 0x75, 0xf5,
    0x0d, 0x8d, 0x4d, 0xcd, 0x2d, 0xad, 0x6d, 0xed,
    0x1d, 0x9d, 0x5d, 0xdd, 0x3d, 0xbd, 0x7d, 0xfd,
    0x03, 0x83, 0x43, 0xc3, 0x23, 0xa3, 0x63, 0xe3,
    0x13, 0x93, 0x53, 0xd3, 0x33, 0xb3, 0x73, 0xf3,
    0x0b, 0x8b, 0x4b, 0xcb, 0x2b, 0xab, 0x6b, 0xeb,
    0x1b, 0x9b, 0x5b, 0xdb, 0x3b, 0xbb, 0x7b, 0xfb,
    0x07, 0x87, 0x47, 0xc7, 0x27, 0xa7, 0x67, 0xe7,
    0x17, 0x97, 0x57, 0xd7, 0x37, 0xb7, 0x77, 0xf7,
    0x0f, 0x8f, 0x4f, 0xcf, 0x2f, 0xaf, 0x6f, 0xef,
    0x1f, 0x9f, 0x5f, 0xdf, 0x3f, 0xbf, 0x7f, 0xff,
};

// reverse bit
static __inline RT_U8 bit_rev8(RT_U8 byte)
{
    return byte_rev_table[byte];
}

// reverse bit
static __inline RT_U16 bit_rev16(RT_U16 x)
{
    return (bit_rev8(x & 0xff) << 8) | bit_rev8(x >> 8);
}

static const RT_U16 crc_table[] = 
{
    0x0000, 0x1081, 0x2102, 0x3183,
    0x4204, 0x5285, 0x6306, 0x7387,
    0x8408, 0x9489, 0xa50a, 0xb58b,
    0xc60c, 0xd68d, 0xe70e, 0xf78f
};

// Initialise the crc calculator 
#define BCSP_CRC_INIT(x) x = 0xffff

static __inline struct sk_buff * skb_alloc(unsigned int len)
{
    struct sk_buff *skb = NULL;
    if ((skb = malloc(len + 8)))
    {
        skb->max_len= len;
        skb->data_len = 0;
    }
    else
    {
        RS_DBG("Error: Allocate skb fails!!!");
        skb = NULL;
    }
    memset(skb->data, 0, len);
    return skb;
}

static __inline void skb_free(struct sk_buff *skb)
{
    free(skb);
    return;
}

// increase the date length in sk_buffer by len,
// and return the increased header pointer
static RT_U8 *skb_put(struct sk_buff* skb, RT_U32 len)
{
    RT_U32 old_len = skb->data_len;
    if((skb->data_len + len) > (skb->max_len))
    {
        RS_DBG("Error: Buffer too small");
        return NULL;
    }
    skb->data_len += len;
    return (skb->data + old_len);
}

// change skb->len to len
// !!! len should less than skb->len
static void skb_trim(struct sk_buff *skb, unsigned int len)
{
    if (skb->data_len > len)
    {
        skb->data_len = len;
    }
    else
    {
        RS_DBG("Error: skb->data_len(%ld) < len(%d)", skb->data_len, len);
    }
}

// decrease the data length in sk_buffer by len,
// and move the content forward to the header.
// the data in header will be removed.
static RT_U8 * skb_pull(struct sk_buff * skb, RT_U32 len)
{
    skb->data_len -= len;
    unsigned char *buf;
    if (!(buf = malloc(skb->data_len))) {
	perror("Unable to allocate file buffer");
	exit(1);
    }
    memcpy(buf, skb->data+len, skb->data_len);
    memcpy(skb->data, buf, skb->data_len);
    free(buf);
    return (skb->data);
}

// add "d" into crc scope, caculate the new crc value
static void bcsp_crc_update(RT_U16 *crc, RT_U8 d)
{
    RT_U16 reg = *crc;

    reg = (reg >> 4) ^ crc_table[(reg ^ d) & 0x000f];
    reg = (reg >> 4) ^ crc_table[(reg ^ (d >> 4)) & 0x000f];

    *crc = reg;
}

struct __una_u16 { RT_U16 x; };
static __inline RT_U16 __get_unaligned_cpu16(const void *p)
{
    const struct __una_u16 *ptr = (const struct __una_u16 *)p;
    return ptr->x;
}


static __inline RT_U16 get_unaligned_be16(const void *p)
{
    return __get_unaligned_cpu16((const RT_U8 *)p);
}

static RT_U16 bscp_get_crc(struct bcsp_struct *bcsp)
{
   RT_U16 crc = 0;
   RT_U8 * data = bcsp->rx_skb->data + bcsp->rx_skb->data_len - 2;
   crc = data[1] + (data[0] << 8);
   return crc;
//    return get_unaligned_be16(&bcsp->rx_skb->data[bcsp->rx_skb->data_len - 2]);
}

// add 0xC0 at the end of skb
static void bcsp_slip_msgdelim(struct sk_buff *skb)
{
    const char pkt_delim = 0xc0;
    memcpy(skb_put(skb, 1), &pkt_delim, 1);
}

// slip encode one bytes: add encoded "c" at the end of skb
static void bcsp_slip_one_byte(struct sk_buff *skb, RT_U8 c)
{
    const RT_S8 esc_c0[2] = { 0xdb, 0xdc };
    const RT_S8 esc_db[2] = { 0xdb, 0xdd };
    const RT_S8 esc_11[2] = { 0xdb, 0xde };
    const RT_S8 esc_13[2] = { 0xdb, 0xdf };

    switch (c) 
    {
    case 0xc0:
        memcpy(skb_put(skb, 2), &esc_c0, 2);
        break;
    case 0xdb:
        memcpy(skb_put(skb, 2), &esc_db, 2);
        break;
    case 0x11:
        memcpy(skb_put(skb, 2), &esc_11, 2);
        break;
    case 0x13:
        memcpy(skb_put(skb, 2), &esc_13, 2);
        break;
    default:
        memcpy(skb_put(skb, 1), &c, 1);
    }
}

// bcsp decode one bytes.
static void bcsp_unslip_one_byte(struct bcsp_struct *bcsp, unsigned char byte)
{
    const RT_U8 c0 = 0xc0, db = 0xdb;
    const RT_U8 oof1 = 0x11, oof2 = 0x13;
    //RS_DBG("HCI 3wire bcsp_unslip_one_byte");

    if (BCSP_ESCSTATE_NOESC == bcsp->rx_esc_state) 
    {
        if (0xdb == byte) 
        {
            bcsp->rx_esc_state = BCSP_ESCSTATE_ESC;
        }
        else
        {
            memcpy(skb_put(bcsp->rx_skb, 1), &byte, 1);
            //Check Pkt Header's CRC enable bit
            if ((bcsp->rx_skb->data[0] & 0x40) != 0 && bcsp->rx_state != BCSP_W4_CRC)
            {
                bcsp_crc_update(&bcsp->message_crc, byte);
            }
            bcsp->rx_count--;
        }
    }
    else if(BCSP_ESCSTATE_ESC == bcsp->rx_esc_state)
    {
        switch (byte) 
        {
        case 0xdc:
            memcpy(skb_put(bcsp->rx_skb, 1), &c0, 1);
            if ((bcsp->rx_skb-> data[0] & 0x40) != 0 && bcsp->rx_state != BCSP_W4_CRC)
                bcsp_crc_update(&bcsp-> message_crc, 0xc0);
            bcsp->rx_esc_state = BCSP_ESCSTATE_NOESC;
            bcsp->rx_count--;
            break;
        case 0xdd:
            memcpy(skb_put(bcsp->rx_skb, 1), &db, 1);
            if ((bcsp->rx_skb-> data[0] & 0x40) != 0 && bcsp->rx_state != BCSP_W4_CRC) 
                bcsp_crc_update(&bcsp-> message_crc, 0xdb);
            bcsp->rx_esc_state = BCSP_ESCSTATE_NOESC;
            bcsp->rx_count--;
            break;
        case 0xde:
            memcpy(skb_put(bcsp->rx_skb, 1), &oof1, 1);
            if ((bcsp->rx_skb-> data[0] & 0x40) != 0 && bcsp->rx_state != BCSP_W4_CRC)
                bcsp_crc_update(&bcsp-> message_crc, oof1);
            bcsp->rx_esc_state = BCSP_ESCSTATE_NOESC;
            bcsp->rx_count--;
            break;
        case 0xdf:
            memcpy(skb_put(bcsp->rx_skb, 1), &oof2, 1);
            if ((bcsp->rx_skb-> data[0] & 0x40) != 0 && bcsp->rx_state != BCSP_W4_CRC) 
                bcsp_crc_update(&bcsp-> message_crc, oof2);
            bcsp->rx_esc_state = BCSP_ESCSTATE_NOESC;
            bcsp->rx_count--;
            break;
        default:
            RS_DBG("Error: Invalid byte %02x after esc byte", byte);
            skb_free(bcsp->rx_skb);
            bcsp->rx_skb = NULL;
            bcsp->rx_state = BCSP_W4_PKT_DELIMITER;
            bcsp->rx_count = 0;
            break;
        }
    }
}

static struct sk_buff * bcsp_prepare_pkt(struct bcsp_struct *bcsp, RT_U8 *data, RT_S32 len, RT_S32 pkt_type)
{
    struct sk_buff *nskb;
    RT_U8 hdr[4];
    RT_U16 BCSP_CRC_INIT(bcsp_txmsg_crc);
    int rel, i;
    //RS_DBG("HCI bcsp_prepare_pkt");   

    switch (pkt_type) 
    {
    case HCI_ACLDATA_PKT:
    case HCI_COMMAND_PKT:
    case HCI_EVENT_PKT:
	rel = 1;	// reliable 
	break;
    case BCSP_ACK_PKT:
    case H5_VDRSPEC_PKT:
    case BCSP_LINK_CTL_PKT:
	rel = 0;	// unreliable 
	break;
    default:
	RS_DBG("Unknown packet type");
	return NULL;
    }                                             

    // Max len of packet: (original len +4(bcsp hdr) +2(crc))*2
    //   (because bytes 0xc0 and 0xdb are escaped, worst case is
    //   when the packet is all made of 0xc0 and 0xdb :) )
    //   + 2 (0xc0 delimiters at start and end). 

    nskb = skb_alloc((len + 6) * 2 + 2);
    if (!nskb)
	return NULL;

    //Add SLIP start byte: 0xc0
    bcsp_slip_msgdelim(nskb);
    // set AckNumber in SlipHeader
    hdr[0] = bcsp->rxseq_txack << 3;
    bcsp->is_txack_req = 0;

    //RS_DBG("We request packet no(%u) to card", bcsp->rxseq_txack);
    RS_DBG("Sending packet with seqno %u and wait %u", bcsp->msgq_txseq, bcsp->rxseq_txack);
    if (rel) 
    {
	// set reliable pkt bit and SeqNumber
	hdr[0] |= 0x80 + bcsp->msgq_txseq;
	//RS_DBG("Sending packet with seqno(%u)", bcsp->msgq_txseq);
	++(bcsp->msgq_txseq);
	bcsp->msgq_txseq = (bcsp->msgq_txseq) & 0x07;
    }

    // set DicPresent bit
    if (bcsp->use_crc)
	hdr[0] |= 0x40;

    // set packet type and payload length
    hdr[1] = ((len << 4) & 0xff) | pkt_type;
    hdr[2] = (RT_U8)(len >> 4);
    // set checksum
    hdr[3] = ~(hdr[0] + hdr[1] + hdr[2]);

    // Put BCSP header */
    for (i = 0; i < 4; i++) 
    {
	bcsp_slip_one_byte(nskb, hdr[i]);

	if (bcsp->use_crc)
	    bcsp_crc_update(&bcsp_txmsg_crc, hdr[i]);
    }

    // Put payload */
    for (i = 0; i < len; i++) 
    {
	bcsp_slip_one_byte(nskb, data[i]);

       if (bcsp->use_crc)
	   bcsp_crc_update(&bcsp_txmsg_crc, data[i]);
    }

    // Put CRC */
    if (bcsp->use_crc) 
    {
	bcsp_txmsg_crc = bit_rev16(bcsp_txmsg_crc);
	bcsp_slip_one_byte(nskb, (RT_U8) ((bcsp_txmsg_crc >> 8) & 0x00ff));
	bcsp_slip_one_byte(nskb, (RT_U8) (bcsp_txmsg_crc & 0x00ff));
    }

    // Add SLIP end byte: 0xc0
    bcsp_slip_msgdelim(nskb); 
    return nskb;
}


static void bcsp_remove_acked_pkt(struct bcsp_struct *bcsp)
{
    int pkts_to_be_removed = 0;
    int seqno = 0;
    int i = 0;

    seqno = bcsp->msgq_txseq;
    //pkts_to_be_removed = GetListLength(bcsp->unacked);

    while (pkts_to_be_removed) 
    {
	if (bcsp->rxack == seqno)
		break;

        pkts_to_be_removed--;
	seqno = (seqno - 1) & 0x07;
    }

    if (bcsp->rxack != seqno)
    {
        RS_DBG("Peer acked invalid packet");
    }

    i = 0;
    //skb_queue_walk_safe(&bcsp->unack, skb, tmp) // remove ack'ed packet from bcsp->unack queue
    for (i = 0; i < 5; ++i)
    {
	if (i >= pkts_to_be_removed)
		break;
	i++;
//	__skb_unlink(skb, &bcsp->unack);
//	skb_free(skb);
    }

//	if (skb_queue_empty(&bcsp->unack))
//		del_timer(&bcsp->tbcsp);
//	spin_unlock_irqrestore(&bcsp->unack.lock, flags);

    if (i != pkts_to_be_removed)
        RS_DBG("Removed only (%u) out of (%u) pkts", i, pkts_to_be_removed);
    
}

static void hci_recv_frame(struct sk_buff *skb) 
{
	int 		len;
	unsigned char 	bcspsync[2]     = {0x01, 0x7E},
			bcspsyncresp[2] = {0x02, 0x7D},
			bcsp_sync_resp_pkt[0x8] = {0xc0, 0x00, 0x2F, 0x00, 0xD0, 0x02, 0x7D, 0xc0},
			bcsp_conf_resp_pkt_to_Ctrl[0x8] = {0xc0, 0x00, 0x2F, 0x00, 0xD0, 0x04, 0x7B, 0xc0},
			bcspconf[3]     = {0x03, 0xFC, 0x10},
			bcspconfresp[3] = {0x04, 0x7B, 0x10},
			rtk_event_command_complete[2] = {0xe, 0x4};
	
    	if(rtk_bcsp.link_estab_state == BCSP_H5_SYNC) {  //sync
		if (!memcmp(skb->data, bcspsync, 2)) 
		{
			printf("Get Sync Pkt\n");
			len = write(serial_fd, &bcsp_sync_resp_pkt,0x8);
		} 
		else if (!memcmp(skb->data, bcspsyncresp, 2))
		{	
			printf("Get Sync Resp Pkt\n");
			rtk_bcsp.link_estab_state = BCSP_H5_CONFIG;
		}
		skb_free(skb);
    	} else if(rtk_bcsp.link_estab_state == BCSP_H5_CONFIG) {  //config
		if (!memcmp(skb->data, bcspsync, 0x2)) {
			len = write(serial_fd, &bcsp_sync_resp_pkt, 0x8);
			printf("Get SYNC pkt-active mode\n");
		}				
		else if (!memcmp(skb->data, bcspconf, 0x2)) {
			len = write(serial_fd, &bcsp_conf_resp_pkt_to_Ctrl, 0x8);
			printf("Get CONFG pkt-active mode\n");
		}
		else if (!memcmp(skb->data, bcspconfresp,  0x2)) {
			printf("Get CONFG resp pkt-active mode\n");
			rtk_bcsp.link_estab_state = BCSP_H5_INIT;//BCSP_H5_PATCH;
		}
		else {
			printf("BCSP_H5_CONFIG receive event\n");
			struct sk_buff *nskb = bcsp_prepare_pkt(&rtk_bcsp, NULL, 0, BCSP_ACK_PKT);
			len = write(serial_fd, nskb->data, nskb->data_len);
			skb_free(nskb);	
		}
		skb_free(skb);
	} else if (rtk_bcsp.link_estab_state == BCSP_H5_INIT)
	{

#if 0   //print pkt data
		printf("BCSP_H5_INIT rx:  ");
		int i;
		for (i=0; i<skb->data_len; i++) {
			printf("%02X ", skb->data[i]);
		}
		printf("\n");
#endif			
		if (!memcmp(skb->data, rtk_event_command_complete, 2))
		{
			printf("WB receive command complete now\n");
			unsigned char changerate[2] = {0x17,0xfc};
			if (!memcmp(&skb->data[3], changerate, 2))
			{
				//command complete for change bdrate
				printf("WB receive command complete for change bd rate now\n");
				if (skb->data[5] == 0)
				{
					printf("receive event for change bdrate success, use new bd rate\n");
				//	guse_init_uart_rate = 0;
				}
				else
				{
					printf("receive event for change bdrate fail(%x), contract Realtek please\n", skb->data[2]);
					//guse_init_uart_rate = 1;
				}
				
				//sending down ack for event
				struct sk_buff *nskb = bcsp_prepare_pkt(&rtk_bcsp, NULL, 0, BCSP_ACK_PKT); //data:len+head:4

				write(serial_fd, nskb->data, nskb->data_len);
				skb_free(nskb);

				skb_free(rtk_bcsp.host_last_cmd);
				rtk_bcsp.link_estab_state = BCSP_H5_PATCH;
			}
		}
		skb_free(skb);
	
	} else if(rtk_bcsp.link_estab_state == BCSP_H5_PATCH) {  //patch
#if 0   //print pkt data
		printf("BCSP_H5_PATCH rx:  ");
		int i;
		for (i=0; i<skb->data_len; i++) {
			printf("%02X ", skb->data[i]);
		}
		printf("\n");
#endif			
		rtk_patch.nRxIndex = skb->data[6];
//		printf("rtk_patch.nRxIndex %d\n", rtk_patch.nRxIndex );
		if (rtk_patch.nRxIndex == rtk_patch.nTotal )
			rtk_bcsp.link_estab_state = BCSP_H5_ACTIVE;	
		skb_free(skb);
	} else {
		perror("active state");
		skb_free(skb);
	}		
}


// after rx data is parsed, and we got a rx frame saved in bcsp->rx_skb,
// this routinue is called.
// things todo in this function:
// 1. check if it's a hci frame, if it is, complete it to bthmini
// 2. see the ack number, free acked frame in queue
// 3. reset bcsp->rx_state, set rx_skb to null.

static void bcsp_complete_rx_pkt(struct bcsp_struct *bcsp)
{
	int pass_up = 1;
	BCSP_PKT_HEADER* bcsp_hdr = NULL;
	//RS_DBG("HCI 3wire bcsp_complete_rx_pkt");
	bcsp_hdr = (BCSP_PKT_HEADER * )(bcsp->rx_skb->data);
	if (bcsp_hdr->ReliablePkt)
	{
		RS_DBG("Received reliable seqno %u from card", bcsp->rxseq_txack);
		bcsp->rxseq_txack = bcsp_hdr->SeqNumber + 1;
		bcsp->rxseq_txack %= 8;
		bcsp->is_txack_req = 1;
		// send down an empty ack if needed. 
	}

	bcsp->rxack = bcsp_hdr->AckNumber;

#if 0   //for debug
	if (bcsp->rx_skb->data[0] & 0x80) {
		RS_DBG("Received reliable seqno %u, ack %d, type %d from card", 
				bcsp->rxseq_txack, bcsp_hdr->AckNumber, bcsp_hdr->PktType);
	} else {
		if((bcsp->rx_skb->data[0] & 0x07) == 0) {
			if((bcsp->rx_skb->data[1] & 0x0f)==0)
				RS_DBG("Received PURE_ACK Number:%d from card",bcsp_hdr->AckNumber);
			else {
				RS_DBG("Received unreliable, ack %d, type %d from card", bcsp_hdr->AckNumber, bcsp_hdr->PktType);
			}
		}
		else {
			RS_DBG("ERROR: Received unreliable with non-zero seqno %u from card", bcsp->rxseq_txack);
		}
	}
#endif
	
	switch (bcsp_hdr->PktType) 
	{
	case HCI_ACLDATA_PKT:
	case HCI_EVENT_PKT:
	case HCI_SCODATA_PKT:
	case HCI_COMMAND_PKT:
	case BCSP_LINK_CTL_PKT:
		pass_up = 1;	
		break;
	default:
		pass_up = 0;
	}
    
	bcsp_remove_acked_pkt(bcsp);

	// decide if we need to pass up. 
	if (pass_up)
	{
		// remove bcsp header and send packet to hci
		skb_pull(bcsp->rx_skb, sizeof(BCSP_PKT_HEADER));
		hci_recv_frame(bcsp->rx_skb);
	 	// should skb be freed here?
	}
	else
	{
		// free skb buffer
		skb_free(bcsp->rx_skb);
	}

	bcsp->rx_state = BCSP_W4_PKT_DELIMITER;
	bcsp->rx_skb = NULL;
}


// Recv data
static int bcsp_recv(struct bcsp_struct *bcsp, void *data, int count)
{
    unsigned char *ptr;
    //RS_DBG("count %d rx_state %d rx_count %ld", count, bcsp->rx_state, bcsp->rx_count);
    ptr = (unsigned char *)data;

#if 0
	unsigned char *temp;
	temp = ptr;
	printf("bcsp rx_state:%x, rx_count:%x\n", bcsp->rx_state, bcsp->rx_count); 
	printf("bcsp_recv rx:  ");
	int i;
	for (i=0; i<count; i++) {
		printf("%02X ", temp[i]);
	}
	printf("\n");
#endif
    while (count) 
    {
        if (bcsp->rx_count) 
        {
            if (*ptr == 0xc0) 
            {
		RS_DBG("Error: short BCSP packet");
                skb_free(bcsp->rx_skb);
                bcsp->rx_state = BCSP_W4_PKT_START;
                bcsp->rx_count = 0;
            } else
                bcsp_unslip_one_byte(bcsp, *ptr);

            ptr++; count--;
            continue;
        }

        switch (bcsp->rx_state) 
        {
        case BCSP_W4_BCSP_HDR:
            // check header checksum. see Core Spec V4 "3-wire uart" page 67
            if ((0xff & (RT_U8) ~ (bcsp->rx_skb->data[0] + bcsp->rx_skb->data[1] +
                bcsp->rx_skb->data[2])) != bcsp->rx_skb->data[3]) 
            {
                RS_DBG("Error: BCSP hdr checksum error!!!");
                skb_free(bcsp->rx_skb);
                bcsp->rx_state = BCSP_W4_PKT_DELIMITER;
                bcsp->rx_count = 0;
                continue;
            }

            if (bcsp->rx_skb->data[0] & 0x80	// reliable pkt /
                && (bcsp->rx_skb->data[0] & 0x07) != bcsp->rxseq_txack) // bcsp->hdr->SeqNumber != bcsp->Rxseq_txack
            {
                RS_DBG("Out-of-order packet arrived, got(%u)expected(%u)",
                    bcsp->rx_skb->data[0] & 0x07, bcsp->rxseq_txack);
                bcsp->is_txack_req = 1;
                //hci_uart_tx_wakeup(hu);			
                skb_free(bcsp->rx_skb);
                bcsp->rx_state = BCSP_W4_PKT_DELIMITER;
                bcsp->rx_count = 0;
		if (rtk_patch.nTxIndex == rtk_patch.nTotal) { //depend on weather remote will reset ack numb or not!!!!!!!!!!!!!!!special
			rtk_bcsp.rxseq_txack = bcsp->rx_skb->data[0] & 0x07;
		}
                continue;
            }
            bcsp->rx_state = BCSP_W4_DATA;

            //payload length: May be 0 
            bcsp->rx_count = (bcsp->rx_skb->data[1] >> 4) + (bcsp->rx_skb->data[2] << 4);	
            continue;
        case BCSP_W4_DATA:
            if (bcsp->rx_skb->data[0] & 0x40) 
            {	// pkt with crc /
                bcsp->rx_state = BCSP_W4_CRC;
                bcsp->rx_count = 2;
            } 
            else
            {                
                bcsp_complete_rx_pkt(bcsp); //Send ACK
                //RS_DBG(DF_SLIP,("--------> BCSP_W4_DATA ACK\n"));             
            }
            continue;

        case BCSP_W4_CRC:
            if (bit_rev16(bcsp->message_crc) != bscp_get_crc(bcsp)) 
            {
                RS_DBG("Checksum failed: computed(%04x)received(%04x)", 
                    bit_rev16(bcsp->message_crc), bscp_get_crc(bcsp));
                skb_free(bcsp->rx_skb);
                bcsp->rx_state = BCSP_W4_PKT_DELIMITER;
                bcsp->rx_count = 0;
                continue;
            }
            skb_trim(bcsp->rx_skb, bcsp->rx_skb->data_len - 2);
            bcsp_complete_rx_pkt(bcsp);
            continue;

        case BCSP_W4_PKT_DELIMITER:
            switch (*ptr) 
            {
            case 0xc0:
                bcsp->rx_state = BCSP_W4_PKT_START;
                break;
            default:
                break;
            }
            ptr++; count--;
            break;

        case BCSP_W4_PKT_START:
            switch (*ptr) 
            {
            case 0xc0:
                ptr++; count--;
                break;
            default:
                bcsp->rx_state = BCSP_W4_BCSP_HDR;
                bcsp->rx_count = 4;
                bcsp->rx_esc_state = BCSP_ESCSTATE_NOESC;
                BCSP_CRC_INIT(bcsp->message_crc);

                // Do not increment ptr or decrement count
                // Allocate packet. Max len of a BCSP pkt= 
                // 0xFFF (payload) +4 (header) +2 (crc) 
                bcsp->rx_skb = skb_alloc(0x1005);
                if (!bcsp->rx_skb) 
                {
                    bcsp->rx_state = BCSP_W4_PKT_DELIMITER;
                    bcsp->rx_count = 0;
                    return 0;
                }
                break;
            }
            break;
        }
    }
    return count;
}




static int read_check(int fd, void *buf, int count)
{
	int res;
	do 
    	{
		res = read(fd, buf, count);
		if (res != -1) 
        	{
			buf += res;
			count -= res;
			return res;
			//printf("res = %d error=%d\n", res, errno);
		}		
	} while (count && (errno == 0 || errno == EINTR));	
	return res;
}


static void bcsp_tshy_sig_alarm(int sig)
{
	unsigned char bcspsync[2] = {0x01, 0x7E};
	static int retries = 0;

	if (retries < bcsp_max_retries) {
		retries++;
		struct sk_buff *nskb = bcsp_prepare_pkt(&rtk_bcsp, bcspsync, sizeof(bcspsync), BCSP_LINK_CTL_PKT);
		int len = write(serial_fd, nskb->data, nskb->data_len);	
#if 0   //print pkt data
		printf("sync tx:  ");
		int i;
		for (i=0; i<nskb->data_len; i++) {
			printf("%02X ", nskb->data[i]);
		}
		printf("\n");
#endif	
		printf("3-wire sync pattern send : %d, len: %d\n", retries, len);
		skb_free(nskb);
		alarm(1);
		return;
	}

	tcflush(serial_fd, TCIOFLUSH);
	fprintf(stderr, "H5 sync timed out\n");
	exit(1);
}

static void bcsp_tconf_sig_alarm(int sig)
{
	unsigned char bcspconf[3] = {0x03, 0xFC, 0x14};
	static int retries = 0;

	if (retries < bcsp_max_retries) {
		retries++;
		struct sk_buff *nskb = bcsp_prepare_pkt(&rtk_bcsp, bcspconf, 3, BCSP_LINK_CTL_PKT);
		int len = write(serial_fd,  nskb->data, nskb->data_len);		
		RS_DBG("3-wire config pattern send : %d , len: %d", retries, len);
		skb_free(nskb);
		alarm(1);
		return;
	}

	tcflush(serial_fd, TCIOFLUSH);
	fprintf(stderr, "H5 config timed out\n");
	exit(1);
}

static void bcsp_tinit_sig_alarm(int sig)
{
	static int retries = 0;
	if (retries < bcsp_max_retries)
	{
		retries++;
        if (rtk_bcsp.host_last_cmd)
		{
			int len = write(serial_fd, rtk_bcsp.host_last_cmd->data, rtk_bcsp.host_last_cmd->data_len);
			RS_DBG("3-wire init re send:%d, len:%d", retries, len);
			alarm(1);
			return;
		}
		else
		{
			RS_DBG("3-wire init timeout without last command stored\n");
		}
	}

	tcflush(serial_fd, TCIOFLUSH);
	fprintf(stderr, "Realtek H5 init process timed out\n");
	exit(1);
}

static void bcsp_tpatch_sig_alarm(int sig)
{
	static int retries = 0;
	printf("WB sending patch timeout\n");
	if (retries < bcsp_max_retries/3) {
		retries++;
		rtk_patch.nNeedRetry = 1;
		alarm(3);
		return;
	}
	fprintf(stderr, "H5 patch timed out\n");
	exit(1);
}

static int hci_download_patch(int dd, int index, uint8_t *data, int len)
{
	unsigned char hcipatch[256] = {0x20, 0xfc, 00};
	unsigned char bytes[READ_DATA_SIZE];	
	int retlen;
	struct sigaction sa;

	sa.sa_handler = bcsp_tpatch_sig_alarm;
	sigaction(SIGALRM, &sa, NULL);

	download_vendor_patch_cp cp;
	memset(&cp, 0, sizeof(cp));
	cp.index = index;
	if (data != NULL) {
		memcpy(cp.data, data, len);
	}

	int nValue = rtk_patch.nTotal|0x80;
	if (index == nValue) {
		rtk_patch.nTxIndex = rtk_patch.nTotal;
	} else {
		rtk_patch.nTxIndex = index;
	}
	hcipatch[2] = len+1;
	memcpy(hcipatch+3, &cp, len+1);

	//printf("bcsp_prepare_pkt rtk_bcsp.rxseq_txack:%d\n", rtk_bcsp.rxseq_txack);
	struct sk_buff *nskb = bcsp_prepare_pkt(&rtk_bcsp, hcipatch, len+4, HCI_COMMAND_PKT); //data:len+head:4
	alarm(3);
retry:
//	printf("nskb:%p, dd:%x\n", nskb, dd);
	len = write(dd, nskb->data, nskb->data_len);
#if 0   //print pkt data
		printf("data tx:  ");
		int i;
		for (i=0; i<nskb->data_len; i++) {
			printf("%02X ", nskb->data[i]);
		}
		printf("\n");
#endif	
//	printf("hci_download_patch nTxIndex:%d nRxIndex: %d\n", rtk_patch.nTxIndex, rtk_patch.nRxIndex);
	//while (rtk_patch.nRxIndex != rtk_patch.nTxIndex && rtk_patch.nTxIndex < rtk_patch.nTotal) {  //receive data and ignore last pkt
	while (rtk_patch.nRxIndex != rtk_patch.nTxIndex ) {  //receive data and wait last pkt
		//printf("to check whether need retry:%x\n", rtk_patch.nNeedRetry);
		if (rtk_patch.nNeedRetry) {
			rtk_patch.nNeedRetry = 0;
			perror("retry");
			goto retry;
		}

    		if ((retlen = read_check(dd, &bytes, READ_DATA_SIZE)) == -1) {
			perror("read fail");
			return -1;
		}
#if 0   //print pkt data
		printf("read_check retlen:%d nTxIndex:%d data:   ",  retlen, rtk_patch.nTxIndex);
		int i;
		for (i=0; i<retlen; i++) {
			printf("%02X ", bytes[i]);
		}
		printf("\n");
#endif			
		bcsp_recv(&rtk_bcsp, &bytes, retlen);
	}

	alarm(0);
	skb_free(nskb);	
	return 0;	
}

static int hci_download_patch_h4(int dd, int index, uint8_t *data, int len)
{
#if 0
	unsigned char hcipatch[257] = {0x01, 0x20, 0xfc, 00};
	unsigned char bytes[READ_DATA_SIZE];	
	int retlen;
	struct sigaction sa;
	alarm(3);

	download_vendor_patch_cp cp;
	memset(&cp, 0, sizeof(cp));
	cp.index = index;
	if (data != NULL) {
		memcpy(cp.data, data, len);
	}

	int nValue = rtk_patch.nTotal|0x80;
	if (index == nValue) {
		rtk_patch.nTxIndex = rtk_patch.nTotal;
	} else {
		rtk_patch.nTxIndex = index;
	}
	hcipatch[3] = len+1;
	memcpy(hcipatch+4, &cp, len+1);

	len = write(dd, hcipatch, len+5);
	while (rtk_patch.nRxIndex != rtk_patch.nTxIndex ) {  //receive data and wait last pkt
    		if ((retlen = read_check(dd, &bytes, READ_DATA_SIZE)) == -1) {
			perror("read fail");
			return -1;
		}
#if 0   //print pkt data
		printf("read_check retlen:%d nTxIndex:%d data:   ",  retlen, rtk_patch.nTxIndex);
		int i;
		for (i=0; i<retlen; i++) {
			printf("%02X ", bytes[i]);
		}
		printf("\n");
#endif			
	}
	alarm(0);	
	return 0;
#endif
	   unsigned char bytes[257];
	   unsigned char buf[257] = {0x01, 0x20, 0xfc, 00};
	 
	   printf("dd:%d, index:%d, len:%d .\n", dd, index, len);
	   if (NULL != data)
	   {
	      memcpy(&buf[5], data, len);
	   }

	   int cur_index = index;
	   int ret_Index = -1;

	   /// Set data struct.
	   buf[3] = len + 1;//add index
	   buf[4] = cur_index;
	   size_t total_len = len + 5;
	   printf("buf[3]:%d, buf[4]:%d, total_len: %d\n", buf[3], buf[4], total_len);
	   
	   /// write
	   uint16_t w_len;
	   printf("dd:%d, total_len: %d\n", dd, total_len);
	   w_len = write(dd, buf, total_len);
	   printf("w_len: %d.\n", w_len);

	   uint16_t res;
	   res = read(dd, bytes, 8);
#if 1
	   printf("r_len: %d.\n", res);
	   int i = 0;
	   for(i = 0; i < 8; i++)
	   {
	      printf("byte[%d] = 0x%x\n", i, bytes[i]);
	   }
#endif	   
	   uint8_t rstatus;
	   if((0x04 == bytes[0]) && (0x20 == bytes[4]) && (0xfc == bytes[5]))
	   {
	      ret_Index = bytes[7];
	      rstatus = bytes[6];
	      printf("---->ret_Index:%d, ----->rstatus:%d\n", ret_Index, rstatus);
	      if(0x00 != rstatus)
	      {
		printf("---->read event status is wrong.\n");
		return -1;
	      }
	   }
	   else
	   {
	       printf("==========>Didn't read curret data.\n");
	       return -1;
	   }
	  
	   return ret_Index;

}

static const char *get_firmware_name()
{
	static char firmware_file_name[PATH_MAX] = {0};
	sprintf(firmware_file_name, FIRMWARE_DIRECTORY"rtl8723as.bin");
	return firmware_file_name;
}

int rtk_get_bt_config(unsigned char** config_buf)
{
	char bt_config_file_name[PATH_MAX] = {0};
	struct stat st;
	size_t filelen;
	int fd;

	sprintf(bt_config_file_name, BT_CONFIG_DIRECTORY"bt_conf_rtk8723.c");

	if (stat(bt_config_file_name, &st) < 0)
	{
		printf("can't access bt config file\n");
		return -1;
	}

	filelen = st.st_size;
	

	if ((fd = open(bt_config_file_name, O_RDONLY)) < 0) {
		perror("Can't open bt config file");
		free(*config_buf);	
		return -1;
	}

	if ((*config_buf = malloc(filelen)) == NULL)
	{
		printf("malloc buffer for config file fail(%x)\n", filelen);
		return -1;
	}

	//
	//we may need to parse this config file. 
	//for easy debug, only get need data.
	
	if (read(fd, *config_buf, filelen) < filelen) {
		perror("Can't load bt config file");
		free(*config_buf);	
		close(fd);
		return -1;
	}

#if 0
	printf("read config file OK\n");
	int i = 0;
	for (i=0; i<filelen; i++)
	{
		printf("%2x ", (*config_buf)[i]);
	}
	printf("\n");
#endif	
	return filelen;
}

static int download_patch_file(int dd, PATCH_PROTOCOL patch_protocol)
{
	struct stat st;
	const char *filename;
	size_t filesize, fwsize;
	int fd, config_file_size;
	uint8_t iCurIndex = 0;
	uint8_t iCurLen = 0;
	uint8_t iEndIndex = 0;
	uint8_t iLastPacketLen = 0;
	uint8_t iAdditionPkt = 0;
	uint8_t iTotalIndex = 0;
	unsigned char *buf, *config_buf = NULL;
	unsigned char *bufpatch;		
		
	filename = get_firmware_name();
	
	if (stat(filename, &st) < 0) {
		perror("Can't access firmware");
		return -1;
	}

	if ((config_file_size = rtk_get_bt_config(&config_buf)) < 0)
	{
		printf("get bluetooth config file error\n");
		return -1;
	}

	fwsize = st.st_size;

	filesize = fwsize + (size_t)config_file_size;	
	//printf("Filename\t%s\n", basename(filename));
	//printf("Filesize\t%zd\n", filesize);

	iEndIndex = (uint8_t)((filesize-1)/PATCH_DATA_FIELD_MAX_SIZE);	
	iLastPacketLen = (filesize)%PATCH_DATA_FIELD_MAX_SIZE;
	//iAdditionPkt = (iEndIndex+1)%8?(8-(iEndIndex+1)%8):0; //for old flow
	iAdditionPkt = (iEndIndex+2)%8?(8-(iEndIndex+2)%8):0; //for new flow
	iTotalIndex = iAdditionPkt + iEndIndex;
	rtk_patch.nTotal = iTotalIndex;	//init TotalIndex

	printf("iEndIndex:%d  iLastPacketLen:%d iAdditionpkt:%d\n", iEndIndex, iLastPacketLen, iAdditionPkt);
	
	if (iLastPacketLen == 0) 
		iLastPacketLen = PATCH_DATA_FIELD_MAX_SIZE;
		
	if (!(buf = malloc(filesize))) {
		perror("Unable to allocate file buffer");
		free(config_buf);	
		return -1;
	}

	if ((fd = open(filename, O_RDONLY)) < 0) {
		perror("Can't open firmware");
		free(config_buf);	
		free(buf);
		return -1;
	}

	if (read(fd, buf, fwsize) < (ssize_t) fwsize) {
		perror("Can't load firmware");
		free(config_buf);	
		free(buf);
		close(fd);
		return -1;
	}

	memcpy(&buf[fwsize], config_buf, config_file_size);
	free(config_buf); //free it when not used immediately	
	bufpatch = buf;
	int i;
	for (i=0; i<=iTotalIndex; i++) {
		if (iCurIndex < iEndIndex) {
			//printf("packet index:%d  iCurIndex:%d\n", i, iCurIndex);
			iCurIndex = iCurIndex&0x7F;
			iCurLen = PATCH_DATA_FIELD_MAX_SIZE;
		}
		else if (iCurIndex == iEndIndex) {	//send last data packet			
			if (iCurIndex == iTotalIndex)
				iCurIndex = iCurIndex | 0x80;
			else
				iCurIndex = iCurIndex&0x7F;
			iCurLen = iLastPacketLen;
			//printf("last data packet index:%d  iCurIndex:%d iLastPacketLen:%d\n", i, iCurIndex, iLastPacketLen);
		}
		else if (iCurIndex < iTotalIndex) {
			iCurIndex = iCurIndex&0x7F;
			bufpatch = NULL;
			iCurLen = 0;
			//printf("addtional packet index:%d  iCurIndex:%d\n", i, iCurIndex);
		}		
		else {				//send end packet
			bufpatch = NULL;
			iCurLen = 0;
			iCurIndex = iCurIndex|0x80;
			printf("end packet index:%d iCurIndex:%d\n", i, iCurIndex);			
		}	
		
		if (patch_protocol == PATCH_PROTOCAL_H4) {
			iCurIndex = hci_download_patch_h4(dd, iCurIndex, bufpatch, iCurLen);
			if ((iCurIndex != i) && (i != rtk_patch.nTotal))
			{ 
			   // check index but ignore last pkt
			   printf("index mismatch i:%d iCurIndex:%d, patch fail\n", i, iCurIndex);
			   goto error;
			}
		}
		else if(patch_protocol == PATCH_PROTOCAL_H5) 
			hci_download_patch(dd, iCurIndex, bufpatch, iCurLen);

		if (iCurIndex < iEndIndex) {
			bufpatch += PATCH_DATA_FIELD_MAX_SIZE;			
		}
		iCurIndex ++;	
	}

	//set last ack packet down
	if (patch_protocol == PATCH_PROTOCAL_H5)
	{
		struct sk_buff *nskb = bcsp_prepare_pkt(&rtk_bcsp, NULL, 0, BCSP_ACK_PKT); //data:len+head:4

		write(dd, nskb->data, nskb->data_len);
		skb_free(nskb);

	}
	//usleep(1000000);   //depend on wait last pkt or not
	free(buf);
	close(fd);
	return 0;

error:
	free(buf);
	close(fd);
	return -1;
}


int rtk_vendor_init(int fd, int speed)
{
	struct sk_buff* cmd_change_bdrate = NULL;
	unsigned char cmd[7] = {0};
	int retlen;
	unsigned char bytes[READ_DATA_SIZE];	

	cmd[0] = 0x17; //ocf
	cmd[1] = 0xfc; //ogf, vendor specified
	
	cmd[2] = 4; //length;

	printf("WB to change baudrate\n");
    switch(speed)
	{
		case 3500000:
			cmd[3] = 0x01;
			cmd[4] = 0x70;
			break;
		case 1500000:
			cmd[3] = 0x03;
			cmd[4] = 0x40;
			break;
		case 115200:
			cmd[3] = 0x1D;
			cmd[4] = 0x70;
			break;
		default: //default 921600 now
			cmd[3] = 0x04;
			cmd[4] = 0x60;
			break;
	}
	cmd[5] = 0;
	cmd[6] = 0;

	cmd_change_bdrate = bcsp_prepare_pkt(&rtk_bcsp, cmd, 7, HCI_COMMAND_PKT);
	if (!cmd_change_bdrate)
	{
		fprintf(stderr, "Realtek Init Vendor fail\n");
		return -1;
	}
	
	rtk_bcsp.host_last_cmd = cmd_change_bdrate;
	alarm(2);
	write(fd, cmd_change_bdrate->data, cmd_change_bdrate->data_len);

	while (rtk_bcsp.link_estab_state == BCSP_H5_INIT) {
    		if ((retlen = read_check(fd, &bytes, READ_DATA_SIZE)) == -1) {
			perror("read fail");
			return -1;
		}
#if 0   //print pkt data
		printf("read event for h5 init:%x\n", retlen);
		int i;
		for (i=0; i<retlen; i++) {
			printf("%02X ", bytes[i]);
		}
		printf("\n");
#endif	
		bcsp_recv(&rtk_bcsp, &bytes, retlen);
	}
	return 0;

}

int rtk_init(int fd, int init_speed, int speed, struct termios *ti)
{
	unsigned char bytes[READ_DATA_SIZE];		
	struct sigaction sa;
	int retlen;	

	RS_DBG("WB to init hciattach");	
	if (set_speed(fd, ti, init_speed) < 0) {
		perror("Can't set default baud rate");
		return -1;
	}

	ti->c_cflag |= PARENB;
	ti->c_cflag &= ~(PARODD);
	if (tcsetattr(fd, TCSANOW, ti) < 0) {
		perror("Can't set port settings");
		return -1;
	}

	alarm(0);
	serial_fd = fd;
	memset(&sa, 0, sizeof(sa));
	sa.sa_flags = SA_NOCLDSTOP;
	sa.sa_handler = bcsp_tshy_sig_alarm;
	sigaction(SIGALRM, &sa, NULL);

	// sync
	bcsp_tshy_sig_alarm(0);
	memset(&rtk_bcsp, 0, sizeof(rtk_bcsp));
	rtk_bcsp.link_estab_state = BCSP_H5_SYNC;
	while (rtk_bcsp.link_estab_state == BCSP_H5_SYNC) {
    		if ((retlen = read_check(fd, &bytes, READ_DATA_SIZE)) == -1) {
			perror("read fail");
			return -1;
		}
		bcsp_recv(&rtk_bcsp, &bytes, retlen);
	}

 	// config
	alarm(0);
	sa.sa_handler = bcsp_tconf_sig_alarm;
	sigaction(SIGALRM, &sa, NULL);
	bcsp_tconf_sig_alarm(0);
	while (rtk_bcsp.link_estab_state == BCSP_H5_CONFIG) {
    		if ((retlen = read_check(fd, &bytes, READ_DATA_SIZE)) == -1) {
			perror("read fail");
			return -1;
		}
#if 0   //print pkt data
		printf("CONFIG data:   ");
		int i;
		for (i=0; i<retlen; i++) {
			printf("%02X ", bytes[i]);
		}
		printf("\n");
#endif	
		bcsp_recv(&rtk_bcsp, &bytes, retlen);
	}
	alarm(0);

	sa.sa_handler = bcsp_tinit_sig_alarm;
	sigaction(SIGALRM, &sa, NULL);

	if (rtk_vendor_init(fd, speed) < 0)
	{
		alarm(0);
		return -1;
	}

	alarm(0);
#if 0
	if (guse_init_uart_rate)
	{
		printf("Use init_speed cause setting new baud rate fail\n");
		u->speed = u->init_speed;
	}
#endif
#if 0 	// download patch file	    	
	//memset(&rtk_bcsp, 0, sizeof(rtk_bcsp));
	memset(&rtk_patch, 0, sizeof(rtk_patch));
	rtk_patch.nRxIndex = -1;

	rtk_bcsp.link_estab_state = BCSP_H5_PATCH;
	if (download_patch_file(fd, PATCH_PROTOCAL_H5) < 0) {
		return -1;
	}	
#endif
	usleep(10000);//delay for change baudrate 2012-6-29 15:01:42.
	return 0;
}



int rtk_post(int fd)
{

#if 1 	// download patch file	    	
	printf("WB to download patch code now\n");
	//alarm(0);
	//memset(&rtk_bcsp, 0, sizeof(rtk_bcsp));
	memset(&rtk_patch, 0, sizeof(rtk_patch));
	rtk_patch.nRxIndex = -1;

	rtk_bcsp.link_estab_state = BCSP_H5_PATCH;
	if (download_patch_file(fd, PATCH_PROTOCAL_H5) < 0) {
		return -1;
	}	
#endif
	return 0;

}

int rtk_init_h4(int fd, int speed, struct termios *ti) 
{
	memset(&rtk_patch, 0, sizeof(rtk_patch));
	rtk_patch.nRxIndex = -1;

	if (download_patch_file(fd, PATCH_PROTOCAL_H4) < 0) {
		return -1;
	}
	return 0;	
}



