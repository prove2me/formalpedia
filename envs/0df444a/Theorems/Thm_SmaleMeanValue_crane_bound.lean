-- Prove2me | Theorems.Thm_SmaleMeanValue_crane_bound
-- name    : SmaleMeanValue.crane_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:34:12.846999+00:00
-- url     : https://prove2.me/theorems/1b78a99d-6a66-4bd9-8090-ba2661a660bb
-- title:
--   Crane (2007): $K < 4 - 2.263/\sqrt d$ for $d \ge 8$
-- statement:
--   Let $d \ge 8$. There is a real constant
--
--   $$
--   K < 4 - \frac{2.263}{\sqrt d}
--   $$
--
--   such that for every complex polynomial $P$ of degree exactly $d$ and every $z \in \mathbb C$ with $P'(z) \neq 0$ there is a critical point $c$ of $P$ with
--
--   $$
--   \left| \frac{P(z) - P(c)}{z - c} \right| \le K\,|P'(z)|.
--   $$
--
--   Equivalently, the best constant in degree $d$ is strictly smaller than $4 - 2.263/\sqrt d$.
-- source:
--   Wikipedia, "Mean value problem", revision oldid=1374678764, https://en.wikipedia.org/w/index.php?title=Mean_value_problem&oldid=1374678764, section "Partial results" ("Edward Crane showed that K < 4 - 2.263/sqrt(d) for d >= 8"); Crane, Bull. LMS 39(5) (2007), 781–791, https://doi.org/10.1112/blms/bdm063

import Mathlib
open Polynomial

namespace SmaleMeanValue

theorem crane_bound (d : ℕ) (hd : 8 ≤ d) :
    ∃ K : ℝ, K < 4 - 2.263 / Real.sqrt d ∧
      ∀ P : ℂ[X], P.natDegree = d → ∀ z : ℂ, P.derivative.eval z ≠ 0 →
        ∃ c : ℂ, P.derivative.eval c = 0 ∧
          ‖(P.eval z - P.eval c) / (z - c)‖ ≤ K * ‖P.derivative.eval z‖ := by sorry

end SmaleMeanValue
