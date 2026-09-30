-- Prove2me | Theorems.Thm_ShorAlgorithms_Reduction_card_twoAdic_le_half
-- name    : ShorAlgorithms.Reduction.card_twoAdic_le_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:40:23.069107+00:00
-- url     : https://prove2.me/theorems/7a5176bc-93aa-422a-a350-471a5ff7661a
-- title:
--   §5, p. 1498 — mod an odd prime power, at most half the units have a given 2-part of their order
-- statement:
--   Let $p$ be an odd prime, $\alpha \ge 1$, and $e \ge 0$. Among the $\varphi(p^\alpha)$ units modulo $p^\alpha$, at most half have order $r$ with $2^e$ the largest power of $2$ dividing $r$:
--
--   $$
--   2 \cdot \#\bigl\{x \in (\mathbb{Z}/p^\alpha)^\times : \nu_2(\operatorname{ord}(x)) = e\bigr\} \le \varphi(p^\alpha).
--   $$
--
--   Equivalently, a uniformly random unit modulo $p^\alpha$ has a prescribed 2-part of its order with probability at most $1/2$. The page derives this from the cyclicity of the unit group modulo an odd prime power.
--
--   **Formalization Note** The count is `Nat.card` of the subtype of units whose order has 2-adic valuation `e` (`padicValNat 2`); orders of units are positive, so the valuation convention `padicValNat 2 0 = 0` is never reached.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1498, §5, "The multiplicative group (mod p^α) for any odd prime power p^α is cyclic [Knuth 1981], so for the odd prime power p_i^{α_i}, the probability is at most 1/2 of choosing an x_i having a particular power of 2 as the largest divisor of its order r_i."

import Mathlib

namespace ShorAlgorithms.Reduction

/-- Shor (1997), §5, p. 1498: for an odd prime power `p^α` (`α ≥ 1`), at most half of the units
mod `p^α` have a prescribed power `2^e` as the largest power of 2 dividing their order. -/
theorem card_twoAdic_le_half (p α e : ℕ) (hp : p.Prime) (hodd : Odd p) (hα : 1 ≤ α) :
    2 * Nat.card {u : (ZMod (p ^ α))ˣ // padicValNat 2 (orderOf u) = e}
      ≤ Nat.totient (p ^ α) := by sorry

end ShorAlgorithms.Reduction
