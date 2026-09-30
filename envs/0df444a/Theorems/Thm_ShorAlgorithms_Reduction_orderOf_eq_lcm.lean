-- Prove2me | Theorems.Thm_ShorAlgorithms_Reduction_orderOf_eq_lcm
-- name    : ShorAlgorithms.Reduction.orderOf_eq_lcm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:32:23.580525+00:00
-- url     : https://prove2.me/theorems/d09188c1-f5f8-4ab4-934d-c1f57558ddd4
-- title:
--   §5, p. 1498 — the order of x mod n is the lcm of its orders mod the prime powers p_i^{α_i}
-- statement:
--   Let $n = \prod_{i=1}^k p_i^{\alpha_i}$ be the prime factorization of $n \ge 1$, let $x$ be a unit modulo $n$ with order $r$, and let $r_i$ be the order of $x \bmod p_i^{\alpha_i}$. Then
--
--   $$
--   r = \operatorname{lcm}(r_1, \dots, r_k).
--   $$
--
--   This reduces questions about the order modulo $n$ to the orders modulo the prime powers, where the unit groups are cyclic when $p_i$ is odd.
--
--   **Formalization Note** The $r_i$ are `localOrder n u p` for `p ∈ n.primeFactors`, and the lcm is `Finset.lcm` over `n.primeFactors` (equal to $1$ when $n = 1$). The hypothesis $0 < n$ replaces Shor's standing "$n$ odd"; oddness is not needed here, while $n = 0$ must be excluded because `ZMod 0` is $\mathbb{Z}$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1498, §5, "Suppose that n = ∏_{i=1}^k p_i^{α_i} is the prime factorization of n. Let r_i be the order of x (mod p_i^{α_i}). Then r is the least common multiple of all the r_i."

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_localOrder

namespace ShorAlgorithms.Reduction

/-- Shor (1997), §5, p. 1498: with `n = ∏ p_i^{α_i}` and `r_i` the order of `x (mod p_i^{α_i})`,
the order `r` of `x (mod n)` is the least common multiple of all the `r_i`. -/
theorem orderOf_eq_lcm (n : ℕ) (hn : 0 < n) (u : (ZMod n)ˣ) :
    orderOf u = n.primeFactors.lcm (localOrder n u) := by sorry

end ShorAlgorithms.Reduction
