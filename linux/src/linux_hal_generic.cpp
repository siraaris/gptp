/******************************************************************************

  Copyright (c) 2009-2012, Intel Corporation
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.

   2. Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.

   3. Neither the name of the Intel Corporation nor the names of its
      contributors may be used to endorse or promote products derived from
      this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
  ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
  LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
  CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
  ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.

******************************************************************************/
#include <linux_hal_generic.hpp>
#include <linux_hal_generic_tsprivate.hpp>
#include <platform.hpp>
#include <avbts_message.hpp>
#include <sys/select.h>
#include <sys/socket.h>
#include <netpacket/packet.h>
#include <errno.h>
#include <linux/ethtool.h>
#include <net/if.h>
#include <linux/sockios.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <fcntl.h>
#include <linux/net_tstamp.h>
#include <linux/ptp_clock.h>
#include <syscall.h>
#include <limits.h>
#include <net/ethernet.h>

#define TX_PHY_TIME 184
#define RX_PHY_TIME 382

static bool normalize_rx_gptp_payload( uint8_t *payload, int &length, uint16_t rx_proto, bool *vlan_tagged )
{
	if( vlan_tagged != NULL ) {
		*vlan_tagged = false;
	}

	/* Some NIC/driver paths hand PF_PACKET/SOCK_DGRAM the inner PTP
	 * protocol in sockaddr_ll while still leaving the leading VLAN TCI
	 * and inner EtherType in the payload. Detect and strip that shim so
	 * the PTP parser sees the real header.
	 */
	if( rx_proto == PTP_ETHERTYPE ) {
		uint16_t embedded_inner;

		if( length >= 4 ) {
			memcpy( &embedded_inner, payload + 2, sizeof(embedded_inner) );
			embedded_inner = PLAT_ntohs( embedded_inner );
			if( embedded_inner == PTP_ETHERTYPE ) {
				memmove( payload, payload + 4, length - 4 );
				length -= 4;
				if( vlan_tagged != NULL ) {
					*vlan_tagged = true;
				}
				return true;
			}
		}
	}

	if( rx_proto == ETH_P_8021Q ) {
		uint16_t inner;

		if( length < 4 ) {
			return false;
		}

		memcpy( &inner, payload + 2, sizeof(inner) );
		inner = PLAT_ntohs( inner );
		if( inner != PTP_ETHERTYPE ) {
			return false;
		}

		memmove( payload, payload + 4, length - 4 );
		length -= 4;
		if( vlan_tagged != NULL ) {
			*vlan_tagged = true;
		}
		return true;
	}

	return rx_proto == PTP_ETHERTYPE;
}

net_result LinuxNetworkInterface::nrecv
( LinkLayerAddress *addr, uint8_t *payload, size_t &length )
{
	fd_set readfds;
	int err;
	int active_sd;
	struct msghdr msg;
	struct cmsghdr *cmsg;
	union {
		char control_data[CMSG_SPACE(256)];
		struct cmsghdr cm;
	} control;
	struct sockaddr_ll remote;
	struct iovec sgentry;
	net_result ret = net_succeed;
	bool got_net_lock;

	LinuxTimestamperGeneric *gtimestamper;
	static bool logged_rx_fallback = false;
	static unsigned int logged_rx_ancillary_debug = 0;
	static unsigned int logged_rx_queue_debug = 0;
	static unsigned int logged_rx_vlan_debug = 0;
	static unsigned int logged_rx_general_debug = 0;

	struct timeval timeout = { 0, 16000 }; // 16 ms

	if( !net_lock.lock( &got_net_lock )) {
		GPTP_LOG_ERROR("A Failed to lock mutex");
		return net_fatal;
	}
	if( !got_net_lock ) {
		return net_trfail;
	}

	for( ;; ) {
		bool packet_is_event;
		bool vlan_tagged = false;
		uint16_t rx_proto;

		FD_ZERO( &readfds );
		FD_SET( sd_event, &readfds );
		FD_SET( sd_general, &readfds );

		active_sd = sd_event > sd_general ? sd_event : sd_general;
		err = select( active_sd+1, &readfds, NULL, NULL, &timeout );
		if( err == 0 ) {
			ret = net_trfail;
			goto done;
		} else if( err == -1 ) {
			if( err == EINTR ) {
				// Caught signal
				GPTP_LOG_ERROR("select() recv signal");
				ret = net_trfail;
				goto done;
			} else {
				GPTP_LOG_ERROR("select() failed");
				ret = net_fatal;
				goto done;
			}
		} else if( !FD_ISSET( sd_event, &readfds ) &&
			   !FD_ISSET( sd_general, &readfds )) {
			ret = net_trfail;
			goto done;
		}
		active_sd = FD_ISSET( sd_event, &readfds ) ? sd_event : sd_general;

		memset( &msg, 0, sizeof( msg ));

		msg.msg_iov = &sgentry;
		msg.msg_iovlen = 1;

		sgentry.iov_base = payload;
		sgentry.iov_len = length;

		memset( &remote, 0, sizeof(remote));
		msg.msg_name = (caddr_t) &remote;
		msg.msg_namelen = sizeof( remote );
		msg.msg_control = &control;
		msg.msg_controllen = sizeof(control);

		err = recvmsg( active_sd, &msg, 0 );
		if( err < 0 ) {
			if( errno == ENOMSG ) {
				GPTP_LOG_ERROR("Got ENOMSG: %s:%d", __FILE__, __LINE__);
				ret = net_trfail;
				goto done;
			}
			GPTP_LOG_ERROR("recvmsg() failed: %s", strerror(errno));
			ret = net_fatal;
			goto done;
		}

		rx_proto = PLAT_ntohs( remote.sll_protocol );
		if( !normalize_rx_gptp_payload( payload, err, rx_proto, &vlan_tagged )) {
			continue;
		}

		if( vlan_tagged && logged_rx_vlan_debug < 12 ) {
			GPTP_LOG_WARNING(
				"RX gPTP VLAN tag stripped: protocol=0x%04x len=%d",
				rx_proto, err );
			++logged_rx_vlan_debug;
		}

		if( err < (int) PTP_COMMON_HDR_LENGTH ) {
			continue;
		}

		packet_is_event = (payload[0] & 0x8) == 0;
		if( active_sd == sd_general && logged_rx_general_debug < 80 ) {
			uint8_t tspec = (payload[0] >> 4) & 0x0F;
			uint8_t msg = payload[0] & 0x0F;
			uint16_t seq = PLAT_ntohs(*((uint16_t *)(payload + PTP_COMMON_HDR_SEQUENCE_ID(PTP_COMMON_HDR_OFFSET))));
			char remote_str[32];
			snprintf(remote_str, sizeof(remote_str),
				 "%02x:%02x:%02x:%02x:%02x:%02x",
				 remote.sll_addr[0], remote.sll_addr[1], remote.sll_addr[2],
				 remote.sll_addr[3], remote.sll_addr[4], remote.sll_addr[5]);
			GPTP_LOG_WARNING(
				"RX general: from=%s proto=0x%04x vlan=%d tspec=%u msg=%u seq=%u len=%d first=%02x %02x %02x %02x",
				remote_str, rx_proto, vlan_tagged ? 1 : 0, tspec, msg, seq, err,
				payload[0], payload[1], payload[2], payload[3]);
			++logged_rx_general_debug;
		}
		if( (active_sd == sd_event && !packet_is_event) ||
		    (active_sd == sd_general && packet_is_event) ) {
			continue;
		}

		*addr = LinkLayerAddress( remote.sll_addr );
		break;
	}

	gtimestamper = dynamic_cast<LinuxTimestamperGeneric *>(timestamper);
	if( active_sd == sd_event && err > 0 && !(payload[0] & 0x8) &&
	    gtimestamper != NULL ) {
		uint16_t rx_sequence_id =
			PLAT_ntohs(*((uint16_t *)(payload + PTP_COMMON_HDR_SEQUENCE_ID(PTP_COMMON_HDR_OFFSET))));
		MessageType rx_message_type =
			(MessageType)(*PTP_COMMON_HDR_TRANSSPEC_MSGTYPE(payload + PTP_COMMON_HDR_OFFSET) & 0xF);
		bool have_rx_timestamp = false;
		bool saw_timestamping_cmsg = false;
		/* Retrieve the timestamp */
		cmsg = CMSG_FIRSTHDR(&msg);
		while( cmsg != NULL ) {
			if( logged_rx_ancillary_debug < 12 ) {
				GPTP_LOG_WARNING(
					"RX event ancillary: msg_flags=0x%x cmsg_level=%d cmsg_type=%d cmsg_len=%zu",
					msg.msg_flags, cmsg->cmsg_level, cmsg->cmsg_type,
					(size_t)cmsg->cmsg_len);
			}
			if
				( cmsg->cmsg_level == SOL_SOCKET &&
				  cmsg->cmsg_type == SO_TIMESTAMPING ) {
				struct timespec *ts = (struct timespec *) CMSG_DATA(cmsg);
				Timestamp chosen;
				bool have_timestamp = false;
				saw_timestamping_cmsg = true;

				if( logged_rx_ancillary_debug < 12 ) {
					GPTP_LOG_WARNING(
						"RX event SO_TIMESTAMPING: sw=%lld.%09ld sys=%lld.%09ld hw=%lld.%09ld",
						(long long) ts[0].tv_sec, ts[0].tv_nsec,
						(long long) ts[1].tv_sec, ts[1].tv_nsec,
						(long long) ts[2].tv_sec, ts[2].tv_nsec);
				}

				/* Prefer raw hardware RX timestamp, then transformed system,
				 * then software time so generic stock-driver paths can still
				 * process event messages when hardware RX timestamps are absent.
				 */
				if( ts[2].tv_sec != 0 || ts[2].tv_nsec != 0 ) {
					chosen = tsToTimestamp( &ts[2] );
					have_timestamp = true;
				}
				else if( ts[1].tv_sec != 0 || ts[1].tv_nsec != 0 ) {
					chosen = tsToTimestamp( &ts[1] );
					have_timestamp = true;
					if( !logged_rx_fallback ) {
						GPTP_LOG_WARNING("Falling back to system RX timestamps on event socket");
						logged_rx_fallback = true;
					}
				}
				else if( ts[0].tv_sec != 0 || ts[0].tv_nsec != 0 ) {
					chosen = tsToTimestamp( &ts[0] );
					have_timestamp = true;
					if( !logged_rx_fallback ) {
						GPTP_LOG_WARNING("Falling back to software RX timestamps on event socket");
						logged_rx_fallback = true;
					}
				}

				if( have_timestamp ) {
					if( logged_rx_queue_debug < 40 ) {
						GPTP_LOG_WARNING(
							"Queue RX timestamp: msgType=%u seq=%u before=%zu source=%s ts=%hu,%u,%u",
							rx_message_type, rx_sequence_id,
							gtimestamper->getQueuedRxTimestampCount(),
							ts[2].tv_sec != 0 || ts[2].tv_nsec != 0 ? "hw" :
							(ts[1].tv_sec != 0 || ts[1].tv_nsec != 0 ? "sys" : "sw"),
							chosen.seconds_ms, chosen.seconds_ls, chosen.nanoseconds);
						++logged_rx_queue_debug;
					}
					gtimestamper->pushRXTimestamp(
						PTPMessageId(rx_message_type, rx_sequence_id), &chosen );
					have_rx_timestamp = true;
				}
			}
			cmsg = CMSG_NXTHDR(&msg,cmsg);
		}
		if( !have_rx_timestamp ) {
			Timestamp system_now, device_now;
			uint32_t local_clock = 0;
			uint32_t nominal_clock_rate = 0;

			if( gtimestamper->HWTimestamper_gettime(
					&system_now, &device_now,
					&local_clock, &nominal_clock_rate )) {
				if( logged_rx_queue_debug < 40 ) {
					GPTP_LOG_WARNING(
						"Queue RX timestamp: msgType=%u seq=%u before=%zu source=phc-now ts=%hu,%u,%u",
						rx_message_type, rx_sequence_id,
						gtimestamper->getQueuedRxTimestampCount(),
						device_now.seconds_ms, device_now.seconds_ls, device_now.nanoseconds);
					++logged_rx_queue_debug;
				}
				gtimestamper->pushRXTimestamp(
					PTPMessageId(rx_message_type, rx_sequence_id), &device_now );
				if( !logged_rx_fallback ) {
					GPTP_LOG_WARNING("Falling back to current PHC time for RX event timestamps");
					logged_rx_fallback = true;
				}
			}
			else if( logged_rx_ancillary_debug < 12 ) {
				GPTP_LOG_WARNING(
					"RX event timestamp fallback failed: saw_timestamping_cmsg=%d msg_flags=0x%x",
					saw_timestamping_cmsg ? 1 : 0, msg.msg_flags);
			}
			if( logged_rx_ancillary_debug < 12 ) {
				++logged_rx_ancillary_debug;
			}
		}
	}

	length = err;

 done:
	if( !net_lock.unlock()) {
		GPTP_LOG_ERROR("A Failed to unlock, %d", err);
		return net_fatal;
	}

	return ret;
}

int findPhcIndex( InterfaceLabel *iface_label ) {
	int sd;
	int ret;
	InterfaceName *ifname;
	struct ethtool_ts_info info;
	struct ifreq ifr;

	if(( ifname = dynamic_cast<InterfaceName *>(iface_label)) == NULL ) {
		GPTP_LOG_ERROR("findPTPIndex requires InterfaceName");
		ret = -1;
		goto done;
	}

	sd = socket( AF_UNIX, SOCK_DGRAM, 0 );
	if( sd < 0 ) {
		GPTP_LOG_ERROR("findPTPIndex: failed to open socket");
		ret = -1;
		goto done;
	}

	memset( &ifr, 0, sizeof(ifr));
	memset( &info, 0, sizeof(info));
	info.cmd = ETHTOOL_GET_TS_INFO;
	ifname->toString( ifr.ifr_name, IFNAMSIZ-1 );
	ifr.ifr_data = (char *) &info;

	if( ioctl( sd, SIOCETHTOOL, &ifr ) < 0 ) {
		GPTP_LOG_ERROR("findPTPIndex: ioctl(SIOETHTOOL) failed");
		ret = -1;
	} else {
		ret = info.phc_index;
	}
	close(sd);
done:
	return ret;
}

LinuxTimestamperGeneric::~LinuxTimestamperGeneric() {
	if( _private != NULL ) delete _private;
#ifdef WITH_IGBLIB
	if( igb_private != NULL ) delete igb_private;
#endif
}

LinuxTimestamperGeneric::LinuxTimestamperGeneric() {
	_private = NULL;
#ifdef WITH_IGBLIB
	igb_private = NULL;
#endif
	sd = -1;
}

bool LinuxTimestamperGeneric::Adjust( void *tmx ) const {
	if( syscall(__NR_clock_adjtime, _private->clockid, tmx ) != 0 ) {
		GPTP_LOG_ERROR("Failed to adjust PTP clock rate");
		return false;
	}
	return true;
}

bool LinuxTimestamperGeneric::HWTimestamper_init
( InterfaceLabel *iface_label, OSNetworkInterface *iface ) {
	cross_stamp_good = false;
	int phc_index;
	char ptp_device[] = PTP_DEVICE;
#ifdef PTP_HW_CROSSTSTAMP
	struct ptp_clock_caps ptp_capability;
#endif
	_private = new LinuxTimestamperGenericPrivate;

	pthread_mutex_init( &_private->cross_stamp_lock, NULL );

	// Determine the correct PTP clock interface
	phc_index = findPhcIndex( iface_label );
	if( phc_index < 0 ) {
		GPTP_LOG_ERROR("Failed to find PTP device index");
		return false;
	}

	snprintf
		( ptp_device+PTP_DEVICE_IDX_OFFS,
		  sizeof(ptp_device)-PTP_DEVICE_IDX_OFFS, "%d", phc_index );
	GPTP_LOG_ERROR("Using clock device: %s", ptp_device);
	phc_fd = open( ptp_device, O_RDWR );
	if( phc_fd == -1 || (_private->clockid = FD_TO_CLOCKID(phc_fd)) == -1 ) {
		GPTP_LOG_ERROR("Failed to open PTP clock device");
		return false;
	}

#ifdef PTP_HW_CROSSTSTAMP
	// Query PTP stack for availability of HW cross-timestamp
	if( ioctl( phc_fd, PTP_CLOCK_GETCAPS, &ptp_capability ) == -1 )
	{
		GPTP_LOG_ERROR("Failed to query PTP clock capabilities");
		return false;
	}
	precise_timestamp_enabled = ptp_capability.cross_timestamping;
#endif

	if( !resetFrequencyAdjustment() ) {
		GPTP_LOG_ERROR("Failed to reset (zero) frequency adjustment");
		return false;
	}

	if( dynamic_cast<LinuxNetworkInterface *>(iface) != NULL ) {
		iface_list.push_front
			( (dynamic_cast<LinuxNetworkInterface *>(iface)) );
	}

	return true;
}

void LinuxTimestamperGeneric::HWTimestamper_reset()
{
	if( !resetFrequencyAdjustment() ) {
		GPTP_LOG_ERROR("Failed to reset (zero) frequency adjustment");
	}
}

int LinuxTimestamperGeneric::HWTimestamper_txtimestamp
( PortIdentity *identity, PTPMessageId messageId, Timestamp &timestamp,
  unsigned &clock_value, bool last )
{
	int err;
	int ret = GPTP_EC_EAGAIN;
	struct msghdr msg;
	struct cmsghdr *cmsg;
	struct sockaddr_ll remote;
	struct iovec sgentry;
	PTPMessageId reflectedMessageId;
	uint8_t reflected_bytes[ETHER_HDR_LEN + 4 + PTP_COMMON_HDR_LENGTH];
	uint16_t sequenceId;
	bool matched_reflected_id = false;
	bool have_timestamp = false;
	union {
		char control_data[CMSG_SPACE(256)];
		struct cmsghdr cm;
	} control;

	if( sd == -1 ) return -1;
	memset( &msg, 0, sizeof( msg ));
	memset( reflected_bytes, 0, sizeof( reflected_bytes ));

	msg.msg_iov = &sgentry;
	msg.msg_iovlen = 1;

	sgentry.iov_base = reflected_bytes;
	sgentry.iov_len = sizeof(reflected_bytes);

	memset( &remote, 0, sizeof(remote));
	msg.msg_name = (caddr_t) &remote;
	msg.msg_namelen = sizeof( remote );
	msg.msg_control = &control;
	msg.msg_controllen = sizeof(control);

	err = recvmsg( sd, &msg, MSG_ERRQUEUE );
	if( err == -1 ) {
		if( errno == EAGAIN ) {
			ret = GPTP_EC_EAGAIN;
			goto done;
		}
		else {
			ret = GPTP_EC_FAILURE;
			goto done;
		}
	}
	{
		static unsigned int logged_tx_parse_debug = 0;
		const size_t candidate_offsets[] = { 0, 4, ETHER_HDR_LEN, ETHER_HDR_LEN + 4 };
		for( unsigned int i = 0; i < sizeof(candidate_offsets) / sizeof(candidate_offsets[0]); ++i ) {
			size_t candidate = candidate_offsets[i];
			uint8_t *gptpCommonHeader;
			if( candidate + PTP_COMMON_HDR_LENGTH > (size_t) err ) {
				continue;
			}
			gptpCommonHeader = reflected_bytes + candidate;
			sequenceId = PLAT_ntohs(
				*((uint16_t *)(PTP_COMMON_HDR_SEQUENCE_ID(gptpCommonHeader))));
			reflectedMessageId.setSequenceId(sequenceId);
			reflectedMessageId.setMessageType(
				(MessageType)(*PTP_COMMON_HDR_TRANSSPEC_MSGTYPE(
					gptpCommonHeader) & 0xF));
			if( messageId == reflectedMessageId ) {
				matched_reflected_id = true;
				break;
			}
			if( logged_tx_parse_debug < 12 ) {
				GPTP_LOG_WARNING(
					"TX timestamp parse miss: want msgType=%u seq=%u candidate_off=%zu got msgType=%u seq=%u",
					messageId.getMessageType(), messageId.getSequenceId(),
					candidate, reflectedMessageId.getMessageType(),
					reflectedMessageId.getSequenceId());
			}
		}
		if( logged_tx_parse_debug < 12 ) {
			GPTP_LOG_WARNING(
				"TX timestamp raw bytes: %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x",
				reflected_bytes[0], reflected_bytes[1], reflected_bytes[2], reflected_bytes[3],
				reflected_bytes[4], reflected_bytes[5], reflected_bytes[6], reflected_bytes[7],
				reflected_bytes[8], reflected_bytes[9], reflected_bytes[10], reflected_bytes[11],
				reflected_bytes[12], reflected_bytes[13], reflected_bytes[14], reflected_bytes[15]);
			++logged_tx_parse_debug;
		}
		if( !matched_reflected_id && logged_tx_parse_debug < 12 ) {
			GPTP_LOG_WARNING("TX timestamp will rely on serialized fallback for msgType=%u seq=%u",
					 messageId.getMessageType(), messageId.getSequenceId());
		}
	}

	// Retrieve the timestamp
	cmsg = CMSG_FIRSTHDR(&msg);
	while( cmsg != NULL ) {
		if( cmsg->cmsg_level == SOL_SOCKET &&
			cmsg->cmsg_type == SO_TIMESTAMPING ) {
			struct timespec *ts_device, *ts_system;
			Timestamp device, system;
			ts_system = ((struct timespec *) CMSG_DATA(cmsg)) + 1;
			system = tsToTimestamp( ts_system );
			ts_device = ts_system + 1; device = tsToTimestamp( ts_device );
			system._version = version;
			device._version = version;
			timestamp = device;
			have_timestamp = true;
			ret = 0;
			break;
		}
		cmsg = CMSG_NXTHDR(&msg,cmsg);
	}

	if( !have_timestamp ) {
		GPTP_LOG_ERROR("Received a error message, but didn't find a valid timestamp");
		ret = GPTP_EC_EAGAIN;
	} else if( !matched_reflected_id ) {
		static unsigned int logged_tx_fallback_debug = 0;
		if( logged_tx_fallback_debug < 12 ) {
			GPTP_LOG_WARNING(
				"Using TX timestamp without reflected message-id match: msgType=%u seq=%u ts=%hu,%u,%u",
				messageId.getMessageType(), messageId.getSequenceId(),
				timestamp.seconds_ms, timestamp.seconds_ls, timestamp.nanoseconds);
			++logged_tx_fallback_debug;
		}
	}

 done:
	if( ret == 0 || last ) {
		net_lock->unlock();
	}

	return ret;
}

bool LinuxTimestamperGeneric::post_init( int ifindex, int sd, TicketingLock *lock ) {
	int timestamp_flags = 0;
	struct ifreq device;
	struct hwtstamp_config hwconfig;
	int err;

	this->sd = sd;
	this->net_lock = lock;

	memset( &device, 0, sizeof(device));
	device.ifr_ifindex = ifindex;
	err = ioctl( sd, SIOCGIFNAME, &device );
	if( err == -1 ) {
		GPTP_LOG_ERROR
			("Failed to get interface name: %s", strerror(errno));
		return false;
	}

	device.ifr_data = (char *) &hwconfig;
	memset( &hwconfig, 0, sizeof( hwconfig ));
	hwconfig.rx_filter = HWTSTAMP_FILTER_PTP_V2_EVENT;
	hwconfig.tx_type = HWTSTAMP_TX_ON;
	err = ioctl( sd, SIOCSHWTSTAMP, &device );
	if( err == -1 ) {
		GPTP_LOG_ERROR
			("Failed to configure timestamping: %s", strerror(errno));
		return false;
	}
	GPTP_LOG_INFO("Configured timestamping on %s: tx_type=%d rx_filter=%d",
		      device.ifr_name, hwconfig.tx_type, hwconfig.rx_filter);

	timestamp_flags |= SOF_TIMESTAMPING_TX_HARDWARE;
	timestamp_flags |= SOF_TIMESTAMPING_RX_HARDWARE;
	timestamp_flags |= SOF_TIMESTAMPING_RX_SOFTWARE;
	timestamp_flags |= SOF_TIMESTAMPING_SOFTWARE;
	timestamp_flags |= SOF_TIMESTAMPING_SYS_HARDWARE;
	timestamp_flags |= SOF_TIMESTAMPING_RAW_HARDWARE;
	err = setsockopt
		( sd, SOL_SOCKET, SO_TIMESTAMPING, &timestamp_flags,
		  sizeof(timestamp_flags) );
	if( err == -1 ) {
		GPTP_LOG_ERROR
			("Failed to configure timestamping on socket: %s",
			  strerror(errno));
		return false;
	}

	return true;
}

#define MAX_NSEC 1000000000

/* Return *a - *b */
static inline ptp_clock_time pct_diff
( struct ptp_clock_time *a, struct ptp_clock_time *b ) {
	ptp_clock_time result;
	if( a->nsec >= b->nsec ) {
		result.nsec = a->nsec - b->nsec;
	} else {
		--a->sec;
		result.nsec = (MAX_NSEC - b->nsec) + a->nsec;
	}
	result.sec = a->sec - b->sec;

	return result;
}

static inline int64_t pctns(struct ptp_clock_time t)
{
	return t.sec * 1000000000LL + t.nsec;
}

static inline Timestamp pctTimestamp( struct ptp_clock_time *t ) {
	Timestamp result;

	result.seconds_ls = t->sec & 0xFFFFFFFF;
	result.seconds_ms = t->sec >> sizeof(result.seconds_ls)*8;
	result.nanoseconds = t->nsec;

	return result;
}

// Use HW cross-timestamp if available
bool LinuxTimestamperGeneric::HWTimestamper_gettime
( Timestamp *system_time, Timestamp *device_time, uint32_t *local_clock,
  uint32_t *nominal_clock_rate ) const
{
	if( phc_fd == -1 )
		return false;

#ifdef PTP_HW_CROSSTSTAMP
	if( precise_timestamp_enabled )
	{
		struct ptp_sys_offset_precise offset;
		memset( &offset, 0, sizeof(offset));
		if( ioctl( phc_fd, PTP_SYS_OFFSET_PRECISE, &offset ) == 0 )
		{
			*device_time = pctTimestamp( &offset.device );
			*system_time = pctTimestamp( &offset.sys_realtime );

			return true;
		}
	}
#endif

	{
		unsigned i;
		struct ptp_clock_time *pct;
		struct ptp_clock_time *system_time_l = NULL, *device_time_l = NULL;
		int64_t interval = LLONG_MAX;
		struct ptp_sys_offset offset;

		memset( &offset, 0, sizeof(offset));
		offset.n_samples = PTP_MAX_SAMPLES;
		if( ioctl( phc_fd, PTP_SYS_OFFSET, &offset ) == -1 )
			return false;

		pct = &offset.ts[0];
		for( i = 0; i < offset.n_samples; ++i ) {
			int64_t interval_t;
			interval_t = pctns(pct_diff( pct+2*i+2, pct+2*i ));
			if( interval_t < interval ) {
				system_time_l = pct+2*i;
				device_time_l = pct+2*i+1;
				interval = interval_t;
			}
		}

		if (device_time_l)
			*device_time = pctTimestamp( device_time_l );
		if (system_time_l)
			*system_time = pctTimestamp( system_time_l );
	}

	return true;
}
