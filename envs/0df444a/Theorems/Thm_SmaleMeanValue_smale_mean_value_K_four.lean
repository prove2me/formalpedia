-- Prove2me | Theorems.Thm_SmaleMeanValue_smale_mean_value_K_four
-- name    : SmaleMeanValue.smale_mean_value_K_four
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:20:27.097515+00:00
-- url     : https://prove2.me/theorems/4831858d-23b9-471a-9fc9-f7165e7ed4b4
-- title:
--   Smale (1981): the mean value inequality with $K = 4$
-- statement:
--   Let $P$ be a complex polynomial of degree $d \ge 2$ and let $z \in \mathbb C$ with $P'(z) \neq 0$. Then there is a critical point $c$ of $P$ such that
--
--   $$
--   \left| \frac{P(z) - P(c)}{z - c} \right| \le 4\,|P'(z)|.
--   $$
--
--   This is Smale's original theorem, which resolved the mean value problem with the constant $K = 4$. It is the uniform benchmark that all later improvements refine.
-- source:
--   Wikipedia, "Mean value problem", revision oldid=1374678764, https://en.wikipedia.org/w/index.php?title=Mean_value_problem&oldid=1374678764, lead section ("initially resolved by Smale for K = 4"); Smale (1981), Bull. AMS 4(1), 1–36, https://doi.org/10.1090/S0273-0979-1981-14858-8

import Mathlib
open Polynomial

namespace SmaleMeanValue

theorem smale_mean_value_K_four (P : ℂ[X]) (hP : 2 ≤ P.natDegree) (z : ℂ)
    (hz : P.derivative.eval z ≠ 0) :
    ∃ c : ℂ, P.derivative.eval c = 0 ∧
      ‖(P.eval z - P.eval c) / (z - c)‖ ≤ 4 * ‖P.derivative.eval z‖ := by sorry

end SmaleMeanValue
