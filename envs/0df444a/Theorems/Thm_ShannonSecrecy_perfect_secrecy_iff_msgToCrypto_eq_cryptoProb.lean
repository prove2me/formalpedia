-- Prove2me | Theorems.Thm_ShannonSecrecy_perfect_secrecy_iff_msgToCrypto_eq_cryptoProb
-- name    : ShannonSecrecy.perfect_secrecy_iff_msgToCrypto_eq_cryptoProb
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:30:31.909692+00:00
-- url     : https://prove2.me/theorems/6a66c9d5-ca92-4391-bdde-22a656652c3c
-- title:
--   Shannon's Theorem 6: perfect secrecy $\iff$ $P_M(E) = P(E)$
-- statement:
--   **Shannon 1949, Theorem 6 (p. 680).** *A necessary and sufficient condition for perfect secrecy is that*
--   $$P_M(E) = P(E) \qquad \text{for all } M \text{ and } E,$$
--   *that is, $P_M(E)$ must be independent of $M$.*
--
--   Fix a finite secrecy system: finite sets of messages $M$, keys $K$ and cryptograms $E$, an injective enciphering map $T_k : M \to E$ for each key $k$, and an a priori key distribution $P(k)$. Write
--   $$P_M(E) \;=\; \sum_{k \,:\, T_k M = E} P(k)$$
--   for the total probability of the keys that carry the message $M$ to the cryptogram $E$, and, for an a priori message distribution $p$,
--   $$P(E) \;=\; \sum_{M} p(M)\, P_M(E), \qquad P_E(M) \;=\; \frac{p(M) P_M(E)}{P(E)} .$$
--
--   The system has **perfect secrecy** when, for every a priori message distribution $p$ and every cryptogram $E$ with $P(E) \neq 0$, the a posteriori probabilities coincide with the a priori ones: $P_E(M) = p(M)$ for all $M$. Requiring this for every $p$ is Shannon's stipulation that the equality hold "independently of the values of $P(M)$" — he explicitly discards the alternative escape $P(M) = 0$.
--
--   The theorem asserts the equivalence of that condition with the statement that, for every a priori message distribution and every message–cryptogram pair, the key weight $P_M(E)$ equals the unconditional cryptogram probability $P(E)$. Equivalently: the total probability of all keys transforming $M_i$ into a given cryptogram $E$ equals that of all keys transforming $M_j$ into the same $E$, for all $M_i$, $M_j$ and $E$.
--
--   This is the structural characterization on which the rest of §10 rests: it is what makes the counting argument for the number of keys, and the Latin-square description of minimal perfect systems, possible.
--
--   **Formalization Note** The right-hand side quantifies over all a priori distributions $p$; since the left-hand side of the equality does not depend on $p$, this is the same as saying that $P_M(E)$ is independent of $M$ together with its common value being $P(E)$. Cryptograms of probability zero are excluded from the definition of perfect secrecy, because the a posteriori probability is a real quotient and is not meaningful there.
-- source:
--   C. E. Shannon, "Communication Theory of Secrecy Systems", Bell System Technical Journal 28(4):656-715, 1949; https://doi.org/10.1002/j.1538-7305.1949.tb00928.x, p. 680, Theorem 6 (Part II, §10 Perfect Secrecy)

import Definitions.Def_shannon_secrecy_system

namespace ShannonSecrecy

theorem perfect_secrecy_iff_msgToCrypto_eq_cryptoProb
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) :
    PerfectSecrecy C ↔
      ∀ p : M → ℝ, IsPMF p → ∀ (m : M) (e : E), msgToCrypto C m e = cryptoProb C p e := by sorry

end ShannonSecrecy
