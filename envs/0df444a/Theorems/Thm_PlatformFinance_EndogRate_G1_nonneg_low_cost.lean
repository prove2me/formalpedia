-- Prove2me | Theorems.Thm_PlatformFinance_EndogRate_G1_nonneg_low_cost
-- name    : PlatformFinance.EndogRate.G1_nonneg_low_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:52.015277+00:00
-- url     : https://prove2.me/theorems/4eeb1116-b522-4154-82a9-416c6aba8bc3
-- title:
--   Proof of Proposition 8 (a), p. 43 — if c ≤ a(1−φ)²/(1+r_f) then G1(r) ≥ 0 on (−1, r_f]
-- statement:
--   Let $a>0$, $0\le\varphi<1$, $c>0$, $r_f\ge0$, and let $G_1$ be the cubic of the proof of Proposition 8. If the cost is low,
--   $$c \le \frac{a(1-\varphi)^2}{1+r_f},$$
--   then $G_1(r)\ge 0$ for every $-1<r\le r_f$.
--
--   Together with the derivative formula, this makes the platform's no-default profit nondecreasing on $(-1, r_f]$, which is case (a) of Proposition 8.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 43, proof of Proposition 8, case (a)

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model

namespace PlatformFinance.EndogRate

/-- Case (a) of the proof of Proposition 8 (p. 43): if `c ≤ a(1 - φ)²/(1 + rf)` then
`G1(r) ≥ 0` for every `-1 < r ≤ rf`. -/
theorem G1_nonneg_low_cost (a φ c rf : ℝ) (ha : 0 < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hcost : c ≤ cbar a φ rf) :
    ∀ r : ℝ, -1 < r → r ≤ rf → 0 ≤ G1 a φ c rf r := by sorry

end PlatformFinance.EndogRate
