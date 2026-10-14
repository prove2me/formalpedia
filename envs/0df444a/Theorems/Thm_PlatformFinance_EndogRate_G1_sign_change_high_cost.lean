-- Prove2me | Theorems.Thm_PlatformFinance_EndogRate_G1_sign_change_high_cost
-- name    : PlatformFinance.EndogRate.G1_sign_change_high_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:37.879346+00:00
-- url     : https://prove2.me/theorems/340cdde8-624a-416d-bd60-5ca4f136fa55
-- title:
--   Proof of Proposition 8 (b), p. 43 — if c > a(1−φ)²/(1+r_f), G1 changes sign once at r7 < r_f
-- statement:
--   Let $a>0$, $0\le\varphi<1$, $c>0$, $r_f\ge0$ with $(1-\varphi)a > c(1+r_f)$, and let $G_1$ be the cubic of the proof of Proposition 8. If the cost is high,
--   $$c > \frac{a(1-\varphi)^2}{1+r_f},$$
--   then there is $r_7$ with $-1<r_7<r_f$ such that
--
--   $$G_1(r)\ge 0 \ \text{ for } -1<r\le r_7, \qquad G_1(r)<0 \ \text{ for } r_7<r\le r_f.$$
--
--   So the platform's no-default profit rises up to $r_7$ and falls on $(r_7, r_f]$, which is case (b) of Proposition 8.
--
--   **Formalization Note** The page calls $r_7$ "the largest solution of $G_1(r)=0$"; the statement asserts the existence of a point with both sign properties instead of naming the root, which carries the same content on $(-1, r_f]$.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 43, proof of Proposition 8, case (b)

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model

namespace PlatformFinance.EndogRate

/-- Case (b) of the proof of Proposition 8 (p. 43): if `c > a(1 - φ)²/(1 + rf)` then there is
`r7 ∈ (-1, rf)` with `G1 ≥ 0` on `(-1, r7]` and `G1 < 0` on `(r7, rf]`. -/
theorem G1_sign_change_high_cost (a φ c rf : ℝ) (ha : 0 < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a) (hcost : cbar a φ rf < c) :
    ∃ r7 : ℝ, -1 < r7 ∧ r7 < rf ∧
      (∀ r : ℝ, -1 < r → r ≤ r7 → 0 ≤ G1 a φ c rf r) ∧
      ∀ r : ℝ, r7 < r → r ≤ rf → G1 a φ c rf r < 0 := by sorry

end PlatformFinance.EndogRate
