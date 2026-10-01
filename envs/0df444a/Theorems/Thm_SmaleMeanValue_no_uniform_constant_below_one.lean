-- Prove2me | Theorems.Thm_SmaleMeanValue_no_uniform_constant_below_one
-- name    : SmaleMeanValue.no_uniform_constant_below_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T21:49:26.184808+00:00
-- url     : https://prove2.me/theorems/f8203a0c-b95b-4dd9-b29c-cd793cc4522d
-- title:
--   No constant $K < 1$ works in all degrees
-- statement:
--   For every real number $K < 1$ there exist a complex polynomial $P$ of degree at least $2$ and a point $z \in \mathbb C$ with $P'(z) \neq 0$ such that every critical point $c$ of $P$ satisfies
--
--   $$
--   \left| \frac{P(z) - P(c)}{z - c} \right| > K\,|P'(z)|.
--   $$
--
--   Thus no constant bound better than $K = 1$ can hold for polynomials of all degrees, which makes $K = 1$ the natural degree-independent form of the conjecture.
-- source:
--   Wikipedia, "Mean value problem", revision oldid=1374678764, https://en.wikipedia.org/w/index.php?title=Mean_value_problem&oldid=1374678764, lead section ("so no constant bound better than K = 1 can exist")

import Mathlib
open Polynomial

namespace SmaleMeanValue

theorem no_uniform_constant_below_one (K : ℝ) (hK : K < 1) :
    ∃ P : ℂ[X], 2 ≤ P.natDegree ∧ ∃ z : ℂ, P.derivative.eval z ≠ 0 ∧
      ∀ c : ℂ, P.derivative.eval c = 0 →
        K * ‖P.derivative.eval z‖ < ‖(P.eval z - P.eval c) / (z - c)‖ := by sorry

end SmaleMeanValue
