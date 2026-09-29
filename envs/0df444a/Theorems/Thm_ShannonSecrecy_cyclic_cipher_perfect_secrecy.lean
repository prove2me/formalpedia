-- Prove2me | Theorems.Thm_ShannonSecrecy_cyclic_cipher_perfect_secrecy
-- name    : ShannonSecrecy.cyclic_cipher_perfect_secrecy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:36:52.301623+00:00
-- url     : https://prove2.me/theorems/418185f7-37e2-4967-baec-51c9710bc003
-- title:
--   The cyclic system $T_i M_j = E_{i+j \bmod n}$ has perfect secrecy
-- statement:
--   **Shannon 1949, §10, p. 681, Fig. 5.** *Perfect secrecy is attainable with exactly as many keys as messages.*
--
--   Number the messages and the cryptograms $1, \dots, n$ and take $n$ equally likely keys, the key $i$ acting by
--   $$T_i M_j = E_s, \qquad s = i + j \ (\mathrm{mod}\ n).$$
--   Then, whatever the a priori message distribution, every cryptogram has probability $1/n$ and the a posteriori probability of each message equals its a priori probability, so the system has perfect secrecy. This is the finite one-time pad: it shows that the bound "at least as many keys as messages" is attained.
--
--   **Formalization Note** The messages, keys and cryptograms are all $\mathbb{Z}/n\mathbb{Z}$ for $n \ge 1$, the enciphering map is $T_k(m) = k + m$, and the key distribution is uniform, $P(k) = 1/n$. Perfect secrecy is the property quantified over all a priori message distributions, so the statement is not about one particular distribution of messages.
-- source:
--   C. E. Shannon, "Communication Theory of Secrecy Systems", Bell System Technical Journal 28(4):656-715, 1949; https://doi.org/10.1002/j.1538-7305.1949.tb00928.x, p. 681 (Part II, §10 Perfect Secrecy, the example accompanying Fig. 5)

import Definitions.Def_shannon_secrecy_system

namespace ShannonSecrecy

theorem cyclic_cipher_perfect_secrecy (n : ℕ) [NeZero n] :
    PerfectSecrecy (cyclicCipher n) := by sorry

end ShannonSecrecy
