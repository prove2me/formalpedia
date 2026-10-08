-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_theorem_3_6
-- name    : PrivateRelease.NetMechanism.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:37.729982+00:00
-- url     : https://prove2.me/theorems/0ab33e71-c647-4aa8-8f01-36e2f3e53306
-- title:
--   Theorem 3.6 — for a finite class C, |N_α(C)| ≤ |X|^{⌈log|C|/α²⌉}
-- statement:
--   Let $X$ be a finite data universe, $C$ a finite class of at least three predicates $\varphi:X\to\{0,1\}$, and $\alpha>0$. A minimum $\alpha$-net $N_\alpha(C)$ for the counting queries of $C$ exists, and
--   $$
--   |N_\alpha(C)|\ \le\ |X|^{\lceil \log|C|/\alpha^2\rceil}.
--   $$
--
--   Combined with Corollary 3.5, it gives the utility of the Net mechanism for finite classes of counting queries.
--
--   **Formalization Note** The exponent is rounded up to an integer, matching the database size of Lemma 3.7. The bound is stated for every minimum net (all have the same size), together with the existence of one. Logarithms are natural; $|C|\ge3$ is the hypothesis of Lemma 3.7.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 9, Theorem 3.6

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_Queries

namespace PrivateRelease.NetMechanism

/-- Theorem 3.6 (p. 9): for any finite class `C` of at least three counting queries, a minimum
α-net exists and every minimum α-net has at most `|X|^{⌈log|C|/α²⌉}` members. -/
theorem theorem_3_6 {X : Type} [Fintype X] (C : Finset (X → Bool)) (α : ℝ) (hC : 3 ≤ C.card)
    (hα : 0 < α) :
    (∃ N : Finset (Database X), IsMinNet (countingClass (C : Set (X → Bool))) α N) ∧
      ∀ N : Finset (Database X), IsMinNet (countingClass (C : Set (X → Bool))) α N →
        N.card ≤ Fintype.card X ^ ⌈Real.log (C.card : ℝ) / α ^ 2⌉₊ := by sorry

end PrivateRelease.NetMechanism
