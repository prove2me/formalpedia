-- Prove2me | Theorems.Thm_ShorAlgorithms_Reduction_card_all_agree_le
-- name    : ShorAlgorithms.Reduction.card_all_agree_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T08:47:14.318949+00:00
-- url     : https://prove2.me/theorems/f95c0755-a05b-4334-8941-9066639dfedd
-- title:
--   §5, p. 1498 — the 2-parts of all k local orders agree with probability at most 1/2^{k−1}
-- statement:
--   Let $n > 1$ be odd with $k$ distinct prime factors $p_1, \dots, p_k$, and for a unit $x$ modulo $n$ let $r_i$ be the order of $x \bmod p_i^{\alpha_i}$. Then the proportion of units $x$ for which $\nu_2(r_1) = \cdots = \nu_2(r_k)$ is at most $1/2^{k-1}$:
--
--   $$
--   2^{k-1} \cdot \#\bigl\{x \in (\mathbb{Z}/n)^\times : \nu_2(r_1) = \cdots = \nu_2(r_k)\bigr\} \le \varphi(n).
--   $$
--
--   By the Chinese remainder theorem a uniform unit modulo $n$ corresponds to independent uniform units modulo each $p_i^{\alpha_i}$, and each successive 2-part agrees with the previous ones with probability at most $1/2$.
--
--   **Formalization Note** $k$ is `n.primeFactors.card`, which is at least $1$ for $n > 1$, so `k - 1` does not truncate. The event is "the 2-adic valuations of `localOrder n u p` coincide for all `p, q ∈ n.primeFactors`".
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1498, §5, "Thus each of these powers of 2 has at most a 50% probability of agreeing with the previous ones, so all k of them agree with probability at most 1/2^{k−1}."

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_localOrder

namespace ShorAlgorithms.Reduction

/-- Shor (1997), §5, p. 1498: for odd `n > 1` with `k` distinct prime factors, the units `x`
for which the 2-adic valuations of all the local orders `r_p` agree form a proportion at most
`1/2^{k-1}` of the `φ(n)` units mod `n`. -/
theorem card_all_agree_le (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    2 ^ (n.primeFactors.card - 1) *
        Nat.card {u : (ZMod n)ˣ // ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
          padicValNat 2 (localOrder n u p) = padicValNat 2 (localOrder n u q)}
      ≤ Nat.totient n := by sorry

end ShorAlgorithms.Reduction
