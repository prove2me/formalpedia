-- Prove2me | Theorems.Thm_SmaleMeanValue_conte_fujikawa_lakic
-- name    : SmaleMeanValue.conte_fujikawa_lakic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:28:06.431456+00:00
-- url     : https://prove2.me/theorems/d64e8986-5af7-4d6b-80c3-8e7340a8c8a9
-- title:
--   Conte–Fujikawa–Lakic (2007): $K \le 4\frac{d-1}{d+1}$
-- statement:
--   Let $P$ be a complex polynomial of degree $d \ge 2$ and let $z \in \mathbb C$ with $P'(z) \neq 0$. Then there is a critical point $c$ of $P$ with
--
--   $$
--   \left| \frac{P(z) - P(c)}{z - c} \right| \le 4\,\frac{d-1}{d+1}\,|P'(z)|.
--   $$
--
--   This improves Smale's constant $4$ for each fixed degree $d$.
-- source:
--   Wikipedia, "Mean value problem", revision oldid=1374678764, https://en.wikipedia.org/w/index.php?title=Mean_value_problem&oldid=1374678764, section "Partial results"; Conte, Fujikawa, Lakic, Proc. AMS 135(10) (2007), 3295–3300, https://doi.org/10.1090/S0002-9939-07-08861-2

import Mathlib
open Polynomial

namespace SmaleMeanValue

theorem conte_fujikawa_lakic (P : ℂ[X]) (hP : 2 ≤ P.natDegree) (z : ℂ)
    (hz : P.derivative.eval z ≠ 0) :
    ∃ c : ℂ, P.derivative.eval c = 0 ∧
      ‖(P.eval z - P.eval c) / (z - c)‖ ≤
        (4 * ((P.natDegree : ℝ) - 1) / ((P.natDegree : ℝ) + 1)) *
          ‖P.derivative.eval z‖ := by sorry

end SmaleMeanValue
