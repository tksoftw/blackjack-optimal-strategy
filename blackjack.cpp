#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <map>
#include <set>
#include <tuple>
#include <iostream>
#include <string>
#include <array>
#include <vector>
#include <iterator>
#include <list>
#include <unordered_map>
#include <cstdint>
#include <chrono>
#include <thread>
#include <sstream>
#include <cstring>
#include <fstream>

#define sleep(s) this_thread::sleep_for(chrono::milliseconds((s) * 1000))

#define MODE_EXIT 0
#define MODE_DECK_EV 1
#define MODE_MOVE_EV 2

using namespace std;

/* 
$ g++ -O3 -fopenmp bj4.cpp
$ time ./a.out
*/


typedef uint64_t Deck;

/*
   get_deck_sum(d): returns total # of cards from ranks 1..10.
   get_card_count(d, c): returns how many of rank c are in Deck d.
   set_card_count(d, c, count), increment_card_count, decrement_card_count
   are helpers for updating deck contents.
   NOTE: c is 1..10. 
*/

inline uint64_t get_mask(int c) {
    // either 0x3FULL for 1 <= c <= 9 or 0xFF for c==10
    return (c == 10) ? 0xFFULL : 0x3FULL;
}

inline int get_shift(int c) {
    // 1..9 each in 6 bits, 10 in 8 bits, offset by 2 at the LSB.
    return 2 + (c - 1) * 6;
}

inline int get_deck_sum(const Deck &d) {
    uint64_t sum = 0;
    for (int i = 1; i <= 9; i++) {
        sum += (d >> get_shift(i)) & 0x3FULL;
    }
    sum += (d >> get_shift(10)) & 0xFFULL;
    return (int) sum;
}

inline int get_card_count(const Deck &d, int c) {
    return int((d >> get_shift(c)) & get_mask(c));
}

inline void set_card_count(Deck &d, int c, int count) {
    uint64_t mask = get_mask(c);
    int shift = get_shift(c);
    d &= ~(mask << shift); // clear bits
    d |= ((uint64_t) count & mask) << shift;
}

inline void increment_card_count(Deck &d, int c) {
    int oldCount = get_card_count(d, c);
    set_card_count(d, c, oldCount + 1); // assumes no overflow
}

inline void decrement_card_count(Deck &d, int c) {
    int oldCount = get_card_count(d, c);
    set_card_count(d, c, oldCount - 1); // assumes no underflow
}

/*
   will store 'deck -> index' in indexer, and 'deck -> best total' in cache.
   The array decks[] of length "num_decks" holds the 64-bit Deck representation
   for each index. deck_mapping[d][c] says: "From deck index d, if draw card c,
   what is the new deck's index?"
*/
unordered_map<Deck,int> indexer;
unordered_map<Deck,int> cache;
int deck_number = 1;

// deck_mapping[d][c] = deck index obtained after drawing card c from deck d
int **deck_mapping;

// store a single 64-bit Deck per index.
Deck *decks;  

/*
  These data structures handle the composition / dealer outcome logic.
  composition_index maps a Deck of "dealer's used cards" -> integer ID.
  composition_cards[comp][i] = how many of rank i are used in that composition.
  composition_values[first_upcard][comp] = final dealer total for that composition
  composition_counts[first_upcard][comp] = how many sequences lead to that composition
  composition_lists[first_upcard][(final_value-17)] = a list of composition IDs that produce final_value
*/
map<Deck,int> composition_index;
int **composition_counts;     // composition_counts[first_upcard][comp] 
int **composition_values;     // composition_values[first_upcard][comp]
int comp_number = 1;
int **composition_cards;      // composition_cards[comp][i] = # of rank i
list<int> **composition_lists; // composition_lists[first_upcard][(final_value-17)]

/*
  Various caches for expected values:
  - cache_dealer[deck_idx][upcard-1][value-17] : Probability that dealer ends on 17..22
  - cache_stand[deck_idx][upcard-1][(total-16)] : EV from standing
  - cache_hit_hard, cache_hit_soft, cache_double_hard, cache_double_soft, cache_split
*/
double ***cache_dealer;
double ***cache_stand;
double ***cache_hit_hard;
double ***cache_hit_soft;
double ***cache_double_hard;
double ***cache_double_soft;
double ***cache_split;

// Forward declaration
double ev_hit_soft(int deck_idx, int total, int upcard);

/*
   Allocates all the global arrays, with some over-estimates for maximum size.
*/
void initialize() {
    int num_decks = 35946;
    deck_mapping = new int*[num_decks];
    for(int i = 0; i < num_decks; i++){
        deck_mapping[i] = new int[11];
        for(int j=0; j<11; j++){
            deck_mapping[i][j] = 0;
        }
    }

    // store each deck as a single 64-bit
    decks = new Deck[num_decks];
    for(int i=0; i<num_decks; i++){
        decks[i] = 0ULL;
    }

    // Overestimate for composition arrays
    int comps = 5000;
    composition_counts = new int*[11]; // 11 possible first_upcards: 1..10
    composition_values = new int*[11];
    composition_lists = new list<int>*[11];
    for(int i=0; i<11; i++){
        composition_counts[i] = new int[comps];
        composition_values[i] = new int[comps];
        composition_lists[i] = new list<int>[6]; // final values 17..22 => 6 possible
        for(int j=0; j<comps; j++){
            composition_counts[i][j] = 0;
            composition_values[i][j] = 0;
        }
    }
    composition_cards = new int*[comps];
    for(int i=0; i<comps; i++){
        composition_cards[i] = new int[11];
        for(int j=0; j<11; j++){
            composition_cards[i][j] = 0;
        }
    }

    // Allocate caches for dealer outcomes and for the various player actions
    cache_dealer = new double**[num_decks];
    cache_stand  = new double**[num_decks];
    cache_hit_hard   = new double**[num_decks];
    cache_hit_soft   = new double**[num_decks];
    cache_double_hard= new double**[num_decks];
    cache_double_soft= new double**[num_decks];
    cache_split      = new double**[num_decks];

    for(int i=0; i<num_decks; i++){
        cache_dealer[i]      = new double*[10];
        cache_stand[i]       = new double*[10];
        cache_hit_hard[i]    = new double*[10];
        cache_hit_soft[i]    = new double*[10];
        cache_double_hard[i] = new double*[10];
        cache_double_soft[i] = new double*[10];
        cache_split[i]       = new double*[10];
        for(int j=0; j<10; j++){
            cache_dealer[i][j]      = new double[6];
            cache_stand[i][j]       = new double[6];
            cache_hit_hard[i][j]    = new double[18];
            cache_hit_soft[i][j]    = new double[10];
            cache_double_hard[i][j] = new double[18];
            cache_double_soft[i][j] = new double[10];
            cache_split[i][j]       = new double[10];

            // Initialize to 0.0
            for(int k=0; k<6; k++){
                cache_dealer[i][j][k] = 0.0;
                cache_stand[i][j][k]  = 0.0;
            }
            for(int k=0; k<18; k++){
                cache_hit_hard[i][j][k]    = 0.0;
                cache_double_hard[i][j][k] = 0.0;
            }
            for(int k=0; k<10; k++){
                cache_hit_soft[i][j][k]    = 0.0;
                cache_double_soft[i][j][k] = 0.0;
                cache_split[i][j][k]       = 0.0;
            }
        }
    }
}

/*
   Simple helper that returns a new Deck with card c added.
*/
Deck add_card(const Deck &d, int c) {
    Deck d2 = d;
    increment_card_count(d2, c);
    return d2;
}

/*
   Returns a new Deck with card c removed.
*/
Deck draw_card(const Deck &d, int c) {
    Deck d2 = d;
    if (get_card_count(d2, c) > 0)
        decrement_card_count(d2, c);
    return d2;
}

/*
   compute_dealer_sequences:
   - first: the upcard (1..10)
   - cards: how many of each rank are used so far in the dealer's sequence
   - total: the current "soft total" or "hard total"
   - soft: whether the dealer has a usable ace counted as 11
   Recursively enumerates all possible sequences the dealer might take
   from that upcard and records them in composition_index / composition_cards.
*/
int compute_dealer_sequences(int first, Deck cards, int total, bool soft = false) {
    // If total > 21 but had a usable ace, reduce by 10
    if(total > 21 && soft){
        return compute_dealer_sequences(first, cards, total - 10, false);
    }
    // If dealer must stand
    if(total > 17 || (total == 17 && !soft)){
        // record this final composition
        if(composition_index.find(cards) == composition_index.end()){
            composition_index[cards] = comp_number++;
            int comp_id = composition_index[cards];
            // store card counts in composition_cards[comp_id][i]
            for(int i=1; i<=10; i++){
                composition_cards[comp_id][i] = get_card_count(cards, i);
            }
        }
        int cid = composition_index[cards];
        composition_values[first][cid] = min(total, 22);
        composition_counts[first][cid]++;
        return 1;
    }
    else {
        int ans = 0;
        for(int c=1; c<11; c++){
            Deck c2 = add_card(cards, c);
            if(soft && c==1) {
                ans += compute_dealer_sequences(first, c2, total + 1, true);
            }
            else if(c==1) {
                ans += compute_dealer_sequences(first, c2, total + 11, true);
            }
            else {
                ans += compute_dealer_sequences(first, c2, total + c, soft);
            }
        }
        return ans;
    }
}

/*
   dealer_sequences: enumerates all dealer possibilities for upcards A..10,
   storing the final compositions in composition_lists, etc.
*/
int dealer_sequences() {
    Deck cards = 0ULL; // no cards used initially
    int ans = 0;
    for(int c=1; c<11; c++){
        int total = (c == 1 ? 11 : c);
        ans += compute_dealer_sequences(c, cards, total, (c==1));
    }
    // Now populate composition_lists[first_upcard][final_value - 17]
    // for all compositions found
    for(int c=1; c<11; c++){
        for(int comp=1; comp<3157; comp++){ // comp_number = 3157
            int count = composition_counts[c][comp];
            if(count > 0){
                int final_value = composition_values[c][comp]; // final dealer total, 17..22
                // put comp in the list of that final_value in [17..22], and final_value-17 in [0..5]
                if(final_value >=17 && final_value <=22){
                    composition_lists[c][final_value - 17].push_front(comp);
                }
            }
        }
    }
    return ans;
}

/*
  Probability that the dealer (with upcard) gets a "natural" blackjack
  i.e., upcard + hole card = (A,10) or (10,A).
  look at the deck to see how many 10s or Aces remain.
*/
double dealer_natural_probability(int deck_idx, int upcard) {
    Deck d = decks[deck_idx];
    int totalCards = get_deck_sum(d);

    // If upcard == 1, the hole card needs to be 10
    if(upcard == 1){
        int count10 = get_card_count(d, 10);
        return double(count10) / double(totalCards);
    }
    // If upcard == 10, the hole card needs to be Ace
    else if(upcard == 10){
        int countA = get_card_count(d, 1);
        return double(countA) / double(totalCards);
    }
    else {
        return 0.0;
    }
}

/*
   Probability the dealer ends with 'value' (17..22), given upcard and deck.
   Condition on "not a dealer natural blackjack".
*/
double dealer_conditional_probability(int deck_idx, int upcard, int value) {
    // store results in cache_dealer[deck_idx][upcard-1][value-17].
    double &cached = cache_dealer[deck_idx][upcard-1][value-17];
    if(cached != 0){
        return cached;
    }
    // Probability of dealer's natural blackjack
    double bj = dealer_natural_probability(deck_idx, upcard);

    // sum up probabilities of all compositions that yield final = value
    // among those that didn't produce a natural blackjack.
    double ans = 0.0;
    Deck d = decks[deck_idx];

    // If value == 21, must exclude the immediate (upcard + hole card) = blackjack part
    // so effectively "21 minus the natural-bj portion."
    if(value == 21){
        ans = 0.0;
    }

    // composition_lists[ upcard ][ value-17 ] holds all composition IDs leading to final 'value'
    for(int comp_id : composition_lists[upcard][value-17]) {
        // the number of sequences that produce that composition
        double proba = (double) composition_counts[upcard][comp_id];
        double denom = (double) get_deck_sum(d);
        bool valid = true;

        // Check if the deck has enough cards to produce that composition
        for(int rank=1; rank<=10; rank++){
            int needed = composition_cards[comp_id][rank];
            int have  = get_card_count(d, rank);
            if(have < needed){
                valid = false;
                break;
            }
        }
        if(!valid) continue;

        // If valid, compute the combinatorial probability of drawing those needed ranks
        // from the deck in any order
        for(int rank=1; rank<=10; rank++){
            int needed = composition_cards[comp_id][rank];
            int have   = get_card_count(d, rank);
            for(int j=0; j<needed; j++){
                proba *= double(have - j) / denom;
                denom -= 1.0;
            }
        }
        ans += proba;
    }

    // Among all dealer final outcomes, must condition on "no immediate bj."
    // The unconditional probability of that final outcome is ans, so the conditional is ans / (1 - bj).
    // If value == 21, remove the portion that was a direct natural bj
    if(value == 21){
        ans -= bj;  // remove that direct portion
    }
    ans /= (1.0 - bj);

    cached = ans;
    return ans;
}

/*
   ev_stand(deck_idx, total, upcard): player's EV if they stand with total in [4..21].
   compute the probability that the dealer ends with 17..22, and see if push, lose, or win.
*/
double ev_stand(int deck_idx, int total, int upcard) {
    // cache_stand[deck_idx][upcard-1][ total-16 ] if total >=16
    int arr_idx = max(total - 16, 0); 
    double &cached = cache_stand[deck_idx][upcard-1][arr_idx];
    if(cached != 0){
        return cached;
    }

    double p17 = dealer_conditional_probability(deck_idx, upcard, 17);
    double p18 = dealer_conditional_probability(deck_idx, upcard, 18);
    double p19 = dealer_conditional_probability(deck_idx, upcard, 19);
    double p20 = dealer_conditional_probability(deck_idx, upcard, 20);
    double p21 = dealer_conditional_probability(deck_idx, upcard, 21);
    double p22 = dealer_conditional_probability(deck_idx, upcard, 22);

    double ev = 0.0;
    // Compare player's total vs dealer final
    if(total < 17)  ev = p22 - (p17 + p18 + p19 + p20 + p21);
    if(total == 17) ev = p22 - (p18 + p19 + p20 + p21);
    if(total == 18) ev = p22 + p17 - (p19 + p20 + p21);
    if(total == 19) ev = p22 + p17 + p18 - (p20 + p21);
    if(total == 20) ev = p22 + p17 + p18 + p19 - (p21);
    if(total == 21) ev = p22 + p17 + p18 + p19 + p20; 

    cached = ev;
    return ev;
}

/*
   ev_hit_hard(deck_idx, total, upcard): EV if have a hard total and decide to "hit".
   either bust or continue (recursively).
*/
double ev_hit_hard(int deck_idx, int total, int upcard) {
    // shift total down by 4 for indexing (so total=4..21 => array idx 0..17)
    double &cached = cache_hit_hard[deck_idx][upcard-1][total-4];
    if(cached != 0){
        return cached;
    }

    Deck d = decks[deck_idx];
    int nCards = get_deck_sum(d);
    double ev = 0.0;
    // For each possible draw c in [1..10], compute probability and outcome
    for(int c=1; c<=10; c++){
        int countC = get_card_count(d, c);
        if(countC <= 0) continue;
        double p = double(countC)/double(nCards);

        int deck2 = deck_mapping[deck_idx][c]; 
        // If c=1 and total+11 <=21, it becomes a soft total of total+11
        if(c==1 && total+11 <= 21){
            double h = ev_hit_soft(deck2, total+11, upcard);
            double s = ev_stand(deck2, total+11, upcard);
            ev += p * max(h, s);
        } else if(total + c <= 21){
            double h = ev_hit_hard(deck2, total + c, upcard);
            double s = ev_stand(deck2, total + c, upcard);
            ev += p * max(h, s);
        } else {
            // bust => EV = -1
            ev -= p;
        }
    }

    cached = ev;
    return ev;        
}

/*
   ev_hit_soft: have a soft total in [12..21], decide to "hit".
*/
double ev_hit_soft(int deck_idx, int total, int upcard) {
    // total in [12..21], index by total-12 => [0..9]
    double &cached = cache_hit_soft[deck_idx][upcard-1][total-12];
    if(cached != 0){
        return cached;
    }

    Deck d = decks[deck_idx];
    int nCards = get_deck_sum(d);

    double ev = 0.0;
    for(int c=1; c<=10; c++){
        int countC = get_card_count(d, c);
        if(countC <= 0) continue;
        double p = double(countC)/double(nCards);

        int deck2 = deck_mapping[deck_idx][c];
        int newTotal = total + c;
        if(newTotal <= 21) {
            double H = ev_hit_soft(deck2, newTotal, upcard);
            double S = ev_stand(deck2, newTotal, upcard);
            ev += p * max(H, S);
        }
        else {
            // If newTotal > 21, can drop 10 once if it was truly soft => newTotal-10
            int altTotal = newTotal - 10;
            double H = ev_hit_hard(deck2, altTotal, upcard);
            double S = ev_stand(deck2, altTotal, upcard);
            ev += p * max(H, S);
        }
    }

    cached = ev;
    return ev;
}

/*
   ev_double_hard: doubling down on a hard total => one card, then forced stand.
   Returns 2 * outcome. 
*/
double ev_double_hard(int deck_idx, int total, int upcard) {
    // index by total-4
    double &cached = cache_double_hard[deck_idx][upcard-1][total-4];
    if(cached != 0){
        return cached;
    }
    Deck d = decks[deck_idx];
    int nCards = get_deck_sum(d);
    double ev = 0.0;
    for(int c=1; c<=10; c++){
        int countC = get_card_count(d, c);
        if(countC <= 0) continue;
        double p = double(countC)/double(nCards);
        int deck2 = deck_mapping[deck_idx][c];

        if(c == 1 && total + 11 <= 21){
            double S = ev_stand(deck2, total+11, upcard);
            ev += p * S;
        } else if (total + c <= 21){
            double S = ev_stand(deck2, total+c, upcard);
            ev += p * S;
        }else {
            // bust => -1
            ev -= p;
        }
    }
    // doubling => multiply final result by 2
    cached = 2.0 * ev;
    return cached;
}

/*
   ev_double_soft: doubling down on a soft total => one card, then forced stand.
*/
double ev_double_soft(int deck_idx, int total, int upcard) {
    // index by total-12
    double &cached = cache_double_soft[deck_idx][upcard-1][total-12];
    if(cached != 0){
        return cached;
    }

    Deck d = decks[deck_idx];
    int nCards = get_deck_sum(d);

    double ev = 0.0;
    for(int c=1; c<=10; c++){
        int countC = get_card_count(d, c);
        if(countC <= 0) continue;
        double p = double(countC)/double(nCards);
        int deck2 = deck_mapping[deck_idx][c];

        int newTotal = total + c;
        // If newTotal > 21 and was soft, can reduce 10 once
        if(newTotal > 21) newTotal -= 10;
        
        double S = ev_stand(deck2, newTotal, upcard);
        ev += p * S;
    }
    // doubling => multiply final result by 2
    cached = 2.0 * ev;
    return cached;
}

/*
   ev_split: if the player splits a pair of 'card', get two separate hands each starting with that 'card' + a next drawn card.
   simplified by returning 2 * (some single-hand EV).
*/
double ev_split(int deck_idx, int card, int upcard) {
    // index by [upcard-1][card-1]
    double &cached = cache_split[deck_idx][upcard-1][card-1];
    if(cached != 0){
        return cached;
    }

    Deck d = decks[deck_idx];
    int nCards = get_deck_sum(d);

    double ev = 0.0;
    for(int c=1; c<=10; c++){
        int countC = get_card_count(d, c);
        if(countC <= 0) continue;
        double p = double(countC)/double(nCards);
        int deck2 = deck_mapping[deck_idx][c];
        double H = 0.0, S = 0.0, D = 0.0;
        if(card == 1) { 
            S = ev_stand(deck2, 11+c, upcard); 
            ev += p*S;
            continue; // don't allow action after split aces
        }
        else if(c == 1){
            H = ev_hit_soft(deck2, 11+card, upcard);
            S = ev_stand(deck2, 11+card, upcard);
            D = ev_double_soft(deck2, 11+card, upcard);
        } else {
            H = ev_hit_hard(deck2, card+c, upcard);
            S = ev_stand(deck2, card+c, upcard);
            D = ev_double_hard(deck2, card+c, upcard);
        }
        ev += p * max(S, max(H, D));
    }
    cached = 2.0 * ev;
    return cached;
}

/*
   compute_ev(deck_idx, card1, card2, dealerUpcard):
   If the player has card1 & card2 vs the dealer upcard, compute the best EV of
   {Hit, Stand, Double, Split, Surrender} ignoring natural-blackjack cases (handled below).
*/
double compute_ev(int deck_idx, int c1, int c2, int upcard) {
    // Check for natural player blackjack
    // Probability the dealer has a hole card giving dealer-BJ if upcard is A or 10 is p4
    Deck d = decks[deck_idx];
    int totalCards = get_deck_sum(d);
    double p4 = 0.0;
    if(upcard == 1)  p4 = double(get_card_count(d, 10))/double(totalCards);
    if(upcard == 10) p4 = double(get_card_count(d, 1))/double(totalCards);

    // If player's first two cards are (A,10) or (10,A), that's a natural 21
    // Player's blackjack typically pays 1.5 unless dealer also has BJ => push
    if( (c1==1 && c2==10) || (c1==10 && c2==1) ){
        return (1.0 - p4)*1.5;
    }

    // If not a natural, check these actions:
    // Hit(H), Stand(S), Double(D), Split(P), Surrender(R). The old code sets R=-2 => no surrender
    double R = -2.0; // no surrender
    double H=-2.0, S=-2.0, P=-2.0, D=-2.0;

    // figure out total or if it’s soft
    bool canSplit = (c1 == c2);
    bool soft     = false;
    int total     = c1 + c2;
    
    if(c1==1 && c2==1){
        // two Aces => soft 12
        total = 12;
        soft = true;
    }
    else if(c1==1 || c2 == 1){
        // have exactly 1 Ace
        total += 10;
        soft = true;
    }

    // Evaluate each non-surrender action:
    if(soft){
        H  = ev_hit_soft(deck_idx, total, upcard);
        S  = ev_stand(deck_idx, total, upcard);
        D = ev_double_soft(deck_idx, total, upcard);
    } else {
        H  = ev_hit_hard(deck_idx, total, upcard);
        S  = ev_stand(deck_idx, total, upcard);
        D = ev_double_hard(deck_idx, total, upcard);
    }
    if(canSplit){
        // Evaluate splitting c1
        P = ev_split(deck_idx, c1, upcard);
    }
    // Best action EV
    double best = max(H, max(S, max(P, max(D, R))));
    // If dealer has BJ => lose our original 1 bet (EV= -1) in that scenario
    // Weighted by p4. So final EV = (1-p4)*best + p4*(-1).
    return (1.0 - p4)*best - p4*1.0;
}

/*
   expected_value_of_game(deck): computes the overall EV for a fresh "deck" if draw 3 initial cards 
   in the sequence: 1) player's first card i, 2) player's second card j, 3) dealer upcard k,
   summing over all i,j,k. Then calling compute_ev(...) to see the player's EV from that scenario.
*/
double expected_value_of_game(const Deck &deck) {
    double ev = 0.0;

    // parallelize over i in [1..10], j in [i..10], k in [1..10], etc.
    // Total number of iterations for the collapsed loop
    int total_iterations = 10 * 10 * 10;

    // Parallelize over the flattened loop
    #pragma omp parallel for reduction(+:ev) schedule(dynamic) num_threads(16)
    for (int n = 0; n < total_iterations; n++) {
        // Compute i, j, k from the flattened index n
        int i = (n / 100) + 1;          // i ranges from 1 to 10
        int j = ((n % 100) / 10) + i;   // j ranges from i to 10
        int k = (n % 10) + 1;           // k ranges from 1 to 10

        // Skip invalid j values (j must be >= i and <= 10)
        if (j < i || j > 10) continue;

        int ci = get_card_count(deck, i);
        if (ci == 0) continue;
        int sumAll = get_deck_sum(deck);
        double p1 = double(ci) / double(sumAll);

        Deck d1 = draw_card(deck, i);

        int cj = get_card_count(d1, j);
        if (cj == 0) continue;
        double p2 = double(cj) / double(get_deck_sum(d1));
        if (i != j) p2 *= 2.0;

        Deck d2 = draw_card(d1, j);

        int ck = get_card_count(d2, k);
        if (ck == 0) continue;
        double p3 = double(ck) / double(get_deck_sum(d2));

        Deck d3 = draw_card(d2, k);
        int idx = indexer[d3];

        double tmp = compute_ev(idx, i, j, k);
        ev += p1 * p2 * p3 * tmp;
    }

    return ev;
}

/*
   Build up deck_mapping[] so that deck_mapping[idx][c] gives the new deck index
   after removing card c from decks[idx].
*/
int recurse_decks(const Deck &d, int total) {
    // If seen d before and recorded a "cache[d]" that is >= this total, skip
    int idx = indexer[d];
    if(idx != 0 && cache[d] <= total){
        return idx;
    }
    if(idx == 0){
        // brand new deck
        indexer[d] = deck_number++;
        decks[indexer[d]] = d;
    }
    cache[d] = total;
    idx = indexer[d];

    // For each possible next card c, if total+c < 22, link deck_mapping[idx][c].
    for(int c=1; c<min(22 - total, 11); c++){
        int idx2 = recurse_decks(draw_card(d, c), total + c);
        deck_mapping[idx][c] = idx2;
    }
    return idx;
}

/*
   all_subdecks(d): tries all triples of drawn cards i,j,k from d, and calls recurse_decks
   on the resulting subdeck, to populate deck_mapping fully.
*/
int all_subdecks(const Deck &d) {
    for(int i=1; i<=10; i++){
        for(int j=1; j<=10; j++){
            for(int k=1; k<=10; k++){
                // remove i, j, k
                Deck d2 = draw_card(draw_card(draw_card(d, i), j), k);
                // recurse_decks(d2, j+k), and if j==k => recurse_decks(d2, j)
                recurse_decks(d2, j+k);
                if(j == k){
                    recurse_decks(d2, j);
                }
            }
        }
    }
    return deck_number;
}

/*
   best_first_action: prints the EV of {Hit,Stand,Double,Split,Surrender} for a brand-new 2-card hand
*/
array<double, 5> best_first_action(int deck_idx, int card1, int card2, int dealer) {
    bool soft = (card1 == 1) || (card2 == 1);
    int total = card1 + card2 + 10*soft;
    double S = ev_stand(deck_idx, total, dealer);
    double H = -2, D = -2, P = -2, R = -0.5;
    R=-2.0; // no surrender
    if(soft){
        H = ev_hit_soft(deck_idx, total, dealer);
        D = ev_double_soft(deck_idx, total, dealer);
    } else {
        H = ev_hit_hard(deck_idx, total, dealer);
        D = ev_double_hard(deck_idx, total, dealer);
    }
    if(card1==card2){
        // can consider splitting
        P = ev_split(deck_idx, card1, dealer);
    }
    // ostringstream oss;
    // // printf("%lf %lf %lf %lf %lf\n", H, S, D, P, R);
    // oss << H << S << D << P << R << endl;
    // string output = oss.str();
    // return output;
    return {H, S, D, P, R};
}

/*
   best_rest_action: prints the EV of {Hit, Stand} for an already-drawn player's hand,
   i.e. have a total + possibly a soft ace, vs the dealer upcard.
*/
array<double, 5> best_rest_action(int deck_idx, int total, int dealer, bool soft) {
    double H=0.0, S=0.0;
    if(soft){
        H = ev_hit_soft(deck_idx, total, dealer);
    } else {
        H = ev_hit_hard(deck_idx, total, dealer);
    }
    S = ev_stand(deck_idx, total, dealer);
    // ostringstream oss;
    // oss << H << " " << S << endl;
    // string output = oss.str();
    // return output;
    return {H, S, -2, -2, -2};
}

/*
   Creates a deck (64-bit) from the 10 input counts array:
   [cA, c2, c3, c4, c5, c6, c7, c8, c9, c10].
*/
Deck create_deck_from_array(int arr[10]) {
    Deck d = 0ULL;
    for(int rank=0; rank<10; rank++){
        set_card_count(d,rank+1,arr[rank]);
    }
    return d;
}

void cleanup() {
    // Free all allocated memory
    for(int i = 0; i < deck_number; i++) {
        delete[] deck_mapping[i];
    }
    delete[] deck_mapping;
    delete[] decks;
    
    for(int i = 0; i < 11; i++) {
        delete[] composition_counts[i];
        delete[] composition_values[i];
        delete[] composition_lists[i];
    }
    delete[] composition_counts;
    delete[] composition_values;
    delete[] composition_lists;
    
    for(int i = 0; i < comp_number; i++) {
        delete[] composition_cards[i];
    }
    delete[] composition_cards;
    
    // Clean up caches
    for(int i = 0; i < 35946; i++) {
        for(int j = 0; j < 10; j++) {
            delete[] cache_dealer[i][j];
            delete[] cache_stand[i][j];
            delete[] cache_hit_hard[i][j];
            delete[] cache_hit_soft[i][j];
            delete[] cache_double_hard[i][j];
            delete[] cache_double_soft[i][j];
            delete[] cache_split[i][j];
        }
        delete[] cache_dealer[i];
        delete[] cache_stand[i];
        delete[] cache_hit_hard[i];
        delete[] cache_hit_soft[i];
        delete[] cache_double_hard[i];
        delete[] cache_double_soft[i];
        delete[] cache_split[i];
    }
    delete[] cache_dealer;
    delete[] cache_stand;
    delete[] cache_hit_hard;
    delete[] cache_hit_soft;
    delete[] cache_double_hard;
    delete[] cache_double_soft;
    delete[] cache_split;
    
    // Reset counters
    deck_number = 1;
    comp_number = 1;
    
    // Clear maps
    indexer.clear();
    cache.clear();
    composition_index.clear();
}

void reinitialize() {
    // Number of decks and composition size must match what was used in initialize()
    int num_decks = 35946;
    int comps = 5000;
    
    // Reset deck_mapping and decks arrays
    for (int i = 0; i < num_decks; i++) {
        for (int j = 0; j < 11; j++) {
            deck_mapping[i][j] = 0;
        }
        decks[i] = 0ULL;
    }
    
    // Reset composition arrays for first-upcards (1..10)
    for (int i = 0; i < 11; i++) {
        for (int j = 0; j < comps; j++) {
            composition_counts[i][j] = 0;
            composition_values[i][j] = 0;
        }
        // Clear the lists for final values 17..22 (6 possible values)
        for (int j = 0; j < 6; j++) {
            composition_lists[i][j].clear();
        }
    }
    
    // Reset composition_cards
    for (int i = 0; i < comps; i++) {
        for (int j = 0; j < 11; j++) {
            composition_cards[i][j] = 0;
        }
    }
    
    // Reset caches for dealer outcomes and player actions.
    for (int i = 0; i < num_decks; i++) {
        for (int j = 0; j < 10; j++) {
            for (int k = 0; k < 6; k++) {
                cache_dealer[i][j][k] = 0.0;
                cache_stand[i][j][k] = 0.0;
            }
            for (int k = 0; k < 18; k++) {
                cache_hit_hard[i][j][k] = 0.0;
                cache_double_hard[i][j][k] = 0.0;
            }
            for (int k = 0; k < 10; k++) {
                cache_hit_soft[i][j][k] = 0.0;
                cache_double_soft[i][j][k] = 0.0;
                cache_split[i][j][k] = 0.0;
            }
        }
    }
    
    // Reset counters and clear maps used in initialization.
    deck_number = 1;
    comp_number = 1;
    indexer.clear();
    cache.clear();
    composition_index.clear();
}


struct Turn {
    Deck deck;
    int upcard;
    vector<int> player_cards;
};

vector<Deck> read_decks(istringstream &iss) {
    int num_deck_states;
    iss >> num_deck_states;
    vector<Deck> deck_states(num_deck_states);

    for (int deck_index = 0; deck_index < num_deck_states; deck_index++) {
        Deck deck;
        for (int card_position = 1; card_position <= 10; card_position++) {
            int card_count;
            iss >> card_count;
            set_card_count(deck, card_position, card_count);
        }
        deck_states[deck_index] = deck;
    }
    return deck_states;
}

Turn read_turn(istringstream &iss) {
    Turn t;
    Deck deck;
    for (int card_position = 1; card_position <= 10; card_position++) {
        int card_count;
        iss >> card_count;
        set_card_count(deck, card_position, card_count);
    }
    int dealer_upcard;
    iss >> dealer_upcard;

    int player_card;
    vector<int> player_cards;
    while (iss >> player_card) {
        player_cards.push_back(player_card);
    }

    t.deck = deck;
    t.upcard = dealer_upcard;
    t.player_cards = player_cards;
    return t;
}

array<double, 5> get_action_evs(Turn &t) {
    Deck original_deck = t.deck;
    Deck new_deck = add_card(original_deck, t.upcard);
    for (const int card : t.player_cards) 
        new_deck = add_card(new_deck, card);
    all_subdecks(new_deck);
    array<double, 5> result = {0};
    if (t.player_cards.size() > 2) {
        bool ace = false;
        int total = 0;
        for (const int &card : t.player_cards) {
            ace |= (card == 1);
            total += card;
        }
        bool soft = ace && (total+10) <= 21;
        total = (soft) ? total+10 : total; // soft ace
        result = best_rest_action(indexer[original_deck], total, t.upcard, soft);
    }
    else if (t.player_cards.size() == 2) {
        result = best_first_action(indexer[original_deck], t.player_cards[0], t.player_cards[1], t.upcard);
    }
    return result;
}

int main(int argc, char *argv[]) {
    initialize();

    if (argc == 1) {
        int arr[10] = {32,32,32,32,32,32,32,32,32,128};
        Deck deck = create_deck_from_array(arr);
        for (int i = 0; i < 10; i++) {
            deck = draw_card(deck, 10);
            dealer_sequences();
            all_subdecks(deck);
            cout << expected_value_of_game(deck) << endl;
            reinitialize();
        }
        cleanup();
        return 0;
    }

    string line;
    while (true) {
        if (!getline(cin, line)) break; // EOF
        
        istringstream iss(line);

        int mode;
        iss >> mode;
        

        switch (mode)
        {
            case MODE_EXIT:
                cleanup();
                return 0;

            case MODE_DECK_EV: {
                vector<Deck> deck_states = read_decks(iss);
                for (Deck &deck : deck_states) {
                    dealer_sequences();
                    all_subdecks(deck);
                    cout << expected_value_of_game(deck) << endl;
                    reinitialize();
                }
                break;
            }
            case MODE_MOVE_EV: {
                Turn t = read_turn(iss);
                dealer_sequences();
                array<double, 5> actions_ev = get_action_evs(t);
                for (const double &action : actions_ev)
                    cout << action << " ";
                cout << endl;
                reinitialize();
                break;
            }
        }
    }
}

// PYBIND11_MODULE(expected_value_module, m) {
//     m.doc() = "expected_value_module"; // Optional module docstring.
//     m.def("get_ev", &get_ev, "Compute expected value from input string",
//           py::arg("input"));
// }