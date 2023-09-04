#include "queue.h"
#include "lib.h"
#include "protocols.h"
#include <string.h>
#include <arpa/inet.h>
#include <fcntl.h>

#define ETHERTYPE_IP 0x0800
#define ETHERTYPE_ARP 0x0806
#define ICMP 1
#define MAX_TTL 64

struct route_table_entry *rtable;
int rtable_size;

struct arp_entry *arp_table = NULL;
int arp_table_size = 0;

/*declarare coada d pachete*/
queue pachet_queue = NULL;

/*structura pentru elementele cozii de pachete*/
struct queue_elem {
	char *buf; /*retin continutul pachetului*/
	size_t len; /*lungimea pachetului*/
	struct route_table_entry *best_route; /*intrarea din tabela de rutare*/
};

/*functie pentru sortarea tabelei de rutare*/
void quicksort(struct route_table_entry *rtable, int left, int right) {
	int i = left;
	int j = right;
	struct route_table_entry aux; // pentru interschimbare
	struct route_table_entry pivot = rtable[(left + right) / 2]; // alegere pivot

	/*tabela de rutare este sortata crescator dupa masca,
	iar daca mastile sunt egale este sortata crescator dupa prefix*/
	/*partitie dupa pivot*/
	while (i <= j) {
		while (ntohl(rtable[i].mask) < ntohl(pivot.mask) ||
			(rtable[i].mask == pivot.mask && ntohl(rtable[i].prefix) < ntohl(pivot.prefix)))
			i++;
		while (ntohl(rtable[j].mask) > ntohl(pivot.mask) ||
			(rtable[j].mask == pivot.mask && ntohl(rtable[j].prefix) > ntohl(pivot.prefix)))
			j--;
		if (i <= j) {
			// interschimbare
			aux = rtable[i];
			rtable[i] = rtable[j];
			rtable[j] = aux;
			i++;
			j--;
		}
	}

	if (left < j)
		quicksort(rtable, left, j);
	if (i < right)
		quicksort(rtable, i, right);
}

/*implementarea functiei de gasire a celei mai bune rute cu cautare binara*/
struct route_table_entry *get_best_route_optim(uint32_t dest_ip) {
	int left = 0;
	int right = rtable_size - 1;
	int middle;
	struct route_table_entry *best_route = NULL;

	while (left <= right) {
		middle = (left + right) / 2;
		if (rtable[middle].prefix == (dest_ip & rtable[middle].mask)) {
				best_route = &rtable[middle];
				/*cand ajung pe acest caz, caut liniar intre left si right pentru a ma asigura 
				ca gasesc cea mai buna ruta*/
				for (int i = left ; i <= right ; i++) {
					if (rtable[i].prefix == (dest_ip & rtable[i].mask)) {
						if (ntohl(best_route->mask) < ntohl(rtable[i].mask)) {
							best_route = &rtable[i];
						}
					}
				}
				break;
		}
		else if (ntohl(rtable[middle].prefix) < (ntohl(dest_ip) & ntohl(rtable[middle].mask))) {
			left = middle + 1;
		}
		else {
			right = middle - 1;	
		}
	}
	return best_route;
}

/*functie care returneaza o intrare in tabela arp, daca exista*/
struct arp_entry *get_arp_entry(uint32_t dest_ip) {
	for (int i = 0 ; i < arp_table_size ; i++) {
		if (arp_table[i].ip == dest_ip) {
			return &arp_table[i];
		}
	}
	return NULL;
}

/*functie pentru adaugarea unei intrari in tabela arp*/
void add_to_arp_table(uint32_t ip, uint8_t *mac) {
	
	for (int i = 0 ; i < arp_table_size ; i++) {
		if (arp_table[i].ip == ip) {
			/*daca exista deja adresa ip in tabela nu o mai adaugam*/
			return;
		}
	}
	/*daca nu am gasit deja intrarea in tabela arp*/
	arp_table[arp_table_size].ip = ip;
	memcpy(arp_table[arp_table_size].mac, mac, 6);
	arp_table_size++; //marim dimensiunea tabelei arp
}

/*functie care verifica adresa mac destinatie a pachetului cu adresa mac a interfetei 
pe care a fost primit pachetul*/ 
int is_pachet_for_router(int interface, uint8_t *dest_mac_pachet) {
	uint8_t mac[6];
	get_interface_mac(interface, mac);
	if (memcmp(mac, dest_mac_pachet, 6) == 0) {
		return 1; // este pentru router
	}

	/*verific daca adresa mac destinatie e adresa de broadcast*/
	uint8_t broadcast_mac[6] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
	if (memcmp(broadcast_mac, dest_mac_pachet, 6) == 0) {
		return 1; // este pentru router
	}

	return 0; // nu e pentru router, pachetul este aruncat
}

/*functie pentru crearea de mesaje icmp de tip Time exceeded si Destination unreachable*/
char *icmp_message(uint8_t type, uint8_t code, char *buf) {
	struct ether_header *eth_hdr = (struct ether_header *)buf;
	struct iphdr *ip_hdr = (struct iphdr *)(buf + sizeof(struct ether_header));
	struct icmphdr *icmp_hdr = (struct icmphdr *)(buf + sizeof(struct ether_header) + sizeof(struct iphdr));
	
	/*interschimb adresele mac pentru ca mesajul icmp
	trebuie trimis inapoi la expeditor*/
	uint8_t aux[6];
	memcpy(aux, eth_hdr->ether_dhost, sizeof(eth_hdr->ether_dhost));
	memcpy(eth_hdr->ether_dhost, eth_hdr->ether_shost, sizeof(eth_hdr->ether_dhost));
	memcpy(eth_hdr->ether_shost, aux, sizeof(eth_hdr->ether_dhost));

	/*maresc dimensiunea totala a headerului ipv4 + date */
	ip_hdr->tot_len = htons(sizeof(struct iphdr) + sizeof(struct icmphdr));
	ip_hdr->protocol = ICMP;
	if (ip_hdr->ttl <= 1) {
		ip_hdr->ttl = MAX_TTL; /*maresc ttl*/
	}

	/*interschimb adresele ip pentru ca
	pachetul trebuie trimis inapoi la expeditor*/
	uint32_t aux_ip = ip_hdr->daddr;
	ip_hdr->daddr = ip_hdr->saddr;
	ip_hdr->saddr = aux_ip;

	/*recalculez checksum pentru ca am schimbat niste campuri din
	headerul ipv4*/
	ip_hdr->check = 0;
	ip_hdr->check = htons(checksum((uint16_t *) ip_hdr, sizeof(struct iphdr)));

	/*completez campurile din headerul icmp si calculez checksumul*/
	icmp_hdr->type = type;
	icmp_hdr->code = code;
	icmp_hdr->checksum = 0;
	icmp_hdr->checksum = htons(checksum((uint16_t *) icmp_hdr, sizeof(struct icmphdr)));

	return buf;
}


int main(int argc, char *argv[])
{
	char buf[MAX_PACKET_LEN];
	

	// Do not modify this line
	init(argc - 2, argv + 2);

	/*tabela de rutare*/
	rtable = malloc(sizeof(struct route_table_entry) * 80000);
	DIE(rtable == NULL, "malloc rtable failed");
	rtable_size = read_rtable(argv[1], rtable);

	/*sortez tabela de rutare*/	
	quicksort(rtable, 0, rtable_size - 1);

    /*tabela arp*/	
	arp_table = malloc(sizeof(struct arp_entry) * 100);
	DIE(arp_table == NULL, "malloc arp table failed");

	while (1) {

		int interface;
		size_t len;

		interface = recv_from_any_link(buf, &len);
		DIE(interface < 0, "recv_from_any_links");

        /*parsarea pachetului*/
		if (len < sizeof(struct ether_header)) {
			/*daca pachetul e prea scurt
			este aruncat*/
			continue;
		} 

		struct ether_header *eth_hdr = (struct ether_header *) buf;
		/* Note that packets received are in network order,
		any header field which has more than 1 byte will need to be conerted to
		host order. For example, ntohs(eth_hdr->ether_type). The oposite is needed when
		sending a packet on the link, */

		/*validare L2*/
		/*routerul trebuie sa considere doar pachetele trimise catre el insusi
		sau pachete arp de tip broadcast*/
		if (is_pachet_for_router(interface, eth_hdr->ether_dhost) == 0) {
			/*daca pachetul nu e pentru router, este aruncat*/
			continue;
		}

		if (ntohs(eth_hdr->ether_type) == ETHERTYPE_ARP) {
			if (len < sizeof(struct ether_header) + sizeof(struct arp_header)) {
				/*daca pachetul e prea scurt
				este aruncat*/
				continue;
			}
			struct arp_header *arp_hdr = (struct arp_header *) (buf + sizeof(struct ether_header));
			if (ntohs(arp_hdr->op) == 1) {
				/*am primit un arp request*/
			 	/*vom genera un arp reply plecand de la request*/
				/*completam adresa de broadcast cu cea a sursei*/
			
				arp_hdr->op = htons(2); 

				/*adresa destinatie devine adresa sursa*/
				memcpy(eth_hdr->ether_dhost, eth_hdr->ether_shost, sizeof(eth_hdr->ether_dhost));
				/*adresa sursa devine adresa interfetei pe care a venit pachetul*/
		 		get_interface_mac(interface, eth_hdr->ether_shost);

				/*interschimbam adresele ip de sender si target*/
				/*reply ul trebuie sa plece pe unde a venit*/
				uint32_t aux = arp_hdr->spa;
				arp_hdr->spa = arp_hdr->tpa;
				arp_hdr->tpa = aux;

				/*adresele hardware de sender si target sunt la fel ca adresele mac din ethernet header*/
				memcpy(arp_hdr->tha, arp_hdr->sha, sizeof(arp_hdr->tha));
				get_interface_mac(interface, arp_hdr->sha);

				/*trimitem reply ul*/
				send_to_link(interface, buf, len);
				continue;
			} else if (ntohs(arp_hdr->op) == 2) {
				/*am primit un arp reply*/
				/*daca nu exista deja adresa ip in arp table, o adaugam
				impreuna cu adresa mac corespunzatoare*/
				add_to_arp_table(arp_hdr->spa, arp_hdr->sha);

				/*daca am primit un arp reply, verificam daca putem trimite un pachet din coada*/
				queue aux_queue = queue_create(); /*cream o coada auxiliara*/
				while (!queue_empty(pachet_queue)) {
					struct queue_elem *elem = queue_deq(pachet_queue);
					struct arp_entry *arp_entry = get_arp_entry(elem->best_route->next_hop);
					if (arp_entry == NULL) {
						/*daca nu gasim o intrare in tabela arp pentru adresa ip a urmatorului hop,
						adaugam pachetul in coada auxiliara*/
						queue_enq(aux_queue, elem);
					} else {
						/*daca gasim o intrare in tabela arp pentru adresa ip a urmatorului hop,
						completam adresele mac destinatie si sursa*/
						/*acum stim adresa mac destinatie a urmatorului hop*/
						/*trimitem pachetul mai departe*/
						struct ether_header *eth_hdr1 = (struct ether_header *) elem->buf;
						memcpy(eth_hdr1->ether_dhost, arp_entry->mac, sizeof(eth_hdr1->ether_dhost));
						get_interface_mac(elem->best_route->interface, eth_hdr1->ether_shost);
						send_to_link(elem->best_route->interface, elem->buf, elem->len);
					}
				}
				free(pachet_queue);
				pachet_queue = NULL;
				pachet_queue = aux_queue; /*vechea coada va pointa catre coada auxiliara*/
				continue;
			}
		} else if (ntohs(eth_hdr->ether_type) == ETHERTYPE_IP) {
			/*am primit un pachet de tip ipv4*/
			if (len < sizeof(struct ether_header) + sizeof(struct iphdr)) {
				/*daca lungimea pachetului este prea mica,
				pachetul este aruncat*/
				continue;
			}
			struct iphdr *ip_hdr = (struct iphdr *) (buf + sizeof(struct ether_header));
			if (ip_hdr->protocol == 1) {
				/*daca pachetul de tip ipv4 contine un mesaj icmp*/
				if (len < sizeof(struct ether_header) + sizeof(struct iphdr) + sizeof(struct icmphdr)) {
					/*daca lungimea pachetului este prea mica,
					pachetul este aruncat*/
					continue;
				}
				/*daca adresa ip destinatie este adresa interfetei pe care a venit pachetul*/ 
				/*inseamna ca am primit un mesaj icmp de tip Echo request*/
				/*trebuie sa raspundem cu un mesaj icmp de tip Echo reply*/
				if (ip_hdr->daddr == inet_addr(get_interface_ip(interface))) {
					struct icmphdr *icmp_hdr = (struct icmphdr *)(buf + sizeof(struct ether_header) + sizeof(struct iphdr));
					if (icmp_hdr->type == 8 && icmp_hdr->code == 0) {
						uint8_t type = 0;
						uint8_t code = 0;

						uint16_t old_checksum = 0;
						old_checksum = ip_hdr->check;
						ip_hdr->check = 0;

						/*verificare checksum*/
						if (old_checksum != htons(checksum((uint16_t *) ip_hdr, sizeof(struct iphdr)))) {
							/*daca checksumul e gresit,
							pachetul este aruncat*/
							continue;
						}

						/*verificare ttl*/
						if (ip_hdr->ttl <= 1) {
							uint8_t type = 11;
							uint8_t code = 0;
				
							send_to_link(interface, icmp_message(type, code, buf), sizeof(struct ether_header) + sizeof(struct iphdr) + sizeof(struct icmphdr));
							continue;
						}
						
						/*decrementare ttl*/
						ip_hdr->ttl--;

						/*interschimbam adresele mac,
						pachetul trebuie sa plece pe unde a venit*/
						uint8_t aux[6];
						memcpy(aux, eth_hdr->ether_dhost, sizeof(eth_hdr->ether_dhost));
						memcpy(eth_hdr->ether_dhost, eth_hdr->ether_shost, sizeof(eth_hdr->ether_dhost));
						memcpy(eth_hdr->ether_shost, aux, sizeof(eth_hdr->ether_dhost));

						/*interschimbam si adresele ip*/
						uint32_t aux_ip = ip_hdr->saddr;
						ip_hdr->saddr = ip_hdr->daddr;
						ip_hdr->daddr = aux_ip;

						/*recalculare checksum pentru ca am schimbat din campurile headerului ipv4*/
						ip_hdr->check = 0;
						ip_hdr->check = htons(checksum((uint16_t *) ip_hdr, sizeof(struct iphdr)));

						/*recalculare checksum pentru ca am schimbat din campurile headerului icmp*/
						icmp_hdr->type = type;
						icmp_hdr->code = code;
						icmp_hdr->checksum = 0;
						icmp_hdr->checksum = htons(checksum((uint16_t *) icmp_hdr, sizeof(struct icmphdr)));

						/*trimitem echo reply*/
						send_to_link(interface, buf, len);
						continue;
					}
				}
			}
			
			/*verificare checksum pentru headerul ipv4*/
			uint16_t old_checksum = 0;
			old_checksum = ip_hdr->check;
			ip_hdr->check = 0;
			
			if (old_checksum != htons(checksum((uint16_t *) ip_hdr, sizeof(struct iphdr)))) {
				/*checksum gresit,
				pachetul trebuie aruncat*/
				continue;
			}

			/*verificare ttl*/
			if (ip_hdr->ttl <= 1) {
				/*campul ttl a expirat, deci trimitem un mesaj icmp de tip
				Time exceeded*/
				uint8_t type = 11;
				uint8_t code = 0;
				
				send_to_link(interface, icmp_message(type, code, buf), sizeof(struct ether_header) + sizeof(struct iphdr) + sizeof(struct icmphdr));
				continue;
			}
			
			
			uint16_t old_ttl;
			old_ttl = ip_hdr->ttl;
			ip_hdr->ttl--;
			
			/*recalculare checksum cu formula pentru ca am schimbat doar ttl-ul*/
			ip_hdr->check = ~(~old_checksum + ~((uint16_t) old_ttl) + (uint16_t)ip_hdr->ttl) - 1;
			
			/*gasim cea mai buna ruta pentru pachet*/
			struct route_table_entry *best_route = get_best_route_optim(ip_hdr->daddr);
			
			if (best_route == NULL) {
				/*nu am gasit urmatorul hop al pachetului, deci trimitem
				un mesaj icmp de tip Destination unreachable*/
				uint8_t type = 3;
				uint8_t code = 0;

				send_to_link(interface, icmp_message(type, code, buf), sizeof(struct ether_header) + sizeof(struct iphdr) + sizeof(struct icmphdr));
				continue;
			}
			/*cautam adresa mac a urmatorului hop in tabela arp*/
			struct arp_entry *arp_entry = get_arp_entry(best_route->next_hop);
		 	if (arp_entry == NULL) {
				/*daca nu am gasit o intrare in tabela arp*/
				/*nu putem trimite pachetul, deci il punem intr-o coada*/
				if (pachet_queue == NULL) {
					pachet_queue = queue_create();
				}
				struct queue_elem *elem = malloc(sizeof(struct queue_elem));
				elem->buf = malloc(len);
				memcpy(elem->buf, buf, len);
				elem->len = len;
				elem->best_route = best_route;
				queue_enq(pachet_queue, elem);

				/*nu am gasit intrare in tabela arp, deci trimitem un arp request catre urmatorul hop
				pentru a-i afla adresa mac*/
				/*generare arp request*/
				char buf_arp[MAX_PACKET_LEN];
				struct ether_header *eth_hdr_for_arp = (struct ether_header *) buf_arp;
				struct arp_header *arp_hdr = (struct arp_header *) (buf_arp + sizeof(struct ether_header));
				eth_hdr_for_arp->ether_type = htons(ETHERTYPE_ARP);
				/*adresa mac destinatie este una de broadcast*/
				memset(eth_hdr_for_arp->ether_dhost, 0xff, sizeof(eth_hdr_for_arp->ether_dhost));
				/*adresa mac sursa e cea a interfetei catre urmatorul hop*/
				get_interface_mac(best_route->interface, eth_hdr_for_arp->ether_shost);
				arp_hdr->htype = htons(1);
				arp_hdr->ptype = htons(ETHERTYPE_IP);
				arp_hdr->hlen = 6;
				arp_hdr->plen = 4;
				arp_hdr->op = htons(1);
				/*adresa hardware a senderului este adresa mac a interfetei catre urmatorul hop*/
				get_interface_mac(best_route->interface, arp_hdr->sha);
				/*adresa ip a senderului este adresa ip a interfetei catre urmatorul hop*/
				arp_hdr->spa = inet_addr(get_interface_ip(best_route->interface));
				/*adresa hardware target este necunoscuta*/
				memset(arp_hdr->tha, 0, sizeof(arp_hdr->tha));
				/*adresa ip target este adresa ip a urmatorului hop*/
				arp_hdr->tpa = best_route->next_hop;	
				/*trimitere arp request*/
				send_to_link(best_route->interface, buf_arp, sizeof(struct ether_header) + sizeof(struct arp_header));
				continue;
			}
			/*daca am gasit o intrare in tabela arp,
			completam adresele mac destinatie si sursa
			si trimitem pachetul*/
			memcpy(eth_hdr->ether_dhost, arp_entry->mac, sizeof(eth_hdr->ether_dhost));
			get_interface_mac(best_route->interface, eth_hdr->ether_shost);
			send_to_link(best_route->interface, buf, len);
			continue;
		}
	}
}
