-- Prove2me | Theorems.Thm_SmaleMeanValue_smale_mean_value_conjecture_optimal
-- name    : SmaleMeanValue.smale_mean_value_conjecture_optimal
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:37:59.318992+00:00
-- url     : https://prove2.me/theorems/e7bf3d3a-81f4-42a2-afbf-bf0bef7504b0
-- title:
--   Smale's conjecture with the optimal constant $\frac{d-1}{d}$
-- statement:
--   Let $P$ be a complex polynomial of degree $d \ge 2$ and let $z \in \mathbb C$ with $P'(z) \neq 0$. Then there is a critical point $c$ of $P$ with
--
--   $$
--   \left| \frac{P(z) - P(c)}{z - c} \right| \le \frac{d-1}{d}\,|P'(z)|.
--   $$
--
--   This is the strong form of Smale's conjecture, with the constant that the example $z^d - dz$ shows to be optimal in each degree. It implies the goal ($K = 1$) and is open; Tischler proved it for polynomials with only real roots and for polynomials whose roots all have the same absolute value.
-- source:
--   Wikipedia, "Mean value problem", revision oldid=1374678764, https://en.wikipedia.org/w/index.php?title=Mean_value_problem&oldid=1374678764, lead section and section "Partial results" (the optimal bound K = (d-1)/d); Tischler (1989); Smale (1981)

import Mathlib
open Polynomial

namespace SmaleMeanValue

theorem smale_mean_value_conjecture_optimal (P : ℂ[X]) (hP : 2 ≤ P.natDegree) (z : ℂ)
    (hz : P.derivative.eval z ≠ 0) :
    ∃ c : ℂ, P.derivative.eval c = 0 ∧
      ‖(P.eval z - P.eval c) / (z - c)‖ ≤
        (((P.natDegree : ℝ) - 1) / P.natDegree) * ‖P.derivative.eval z‖ := by sorry

end SmaleMeanValue
