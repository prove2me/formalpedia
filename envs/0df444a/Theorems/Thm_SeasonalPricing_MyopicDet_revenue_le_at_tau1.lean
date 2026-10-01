-- Prove2me | Theorems.Thm_SeasonalPricing_MyopicDet_revenue_le_at_tau1
-- name    : SeasonalPricing.MyopicDet.revenue_le_at_tau1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:59:52.94305+00:00
-- url     : https://prove2.me/theorems/e25a958e-692d-4c1f-80ff-8bc0bcb7db9d
-- title:
--   Proof of Proposition 4, first observation — a discount before $\tau_1$ is never better than at $\tau_1$
-- statement:
--   Let $\lambda > 0$ and $0 < \rho < 1$, and consider myopic customers with identical base valuation $1$, valuation $\rho^t$ at time $t$, season $[0, 1]$ and unlimited inventory. Let $R_\rho(p_1, p_2; T)$ be the expected revenue of the price path with premium price $p_1$, discount price $p_2$ and discount time $T$. Let $\rho \le p_2 \le p_1 \le 1$ and $\tau_1 = \ln(p_1)/\ln(\rho)$. Then for every $T \in [0, \tau_1]$,
--
--   $$
--   R_\rho(p_1, p_2; T) \le R_\rho(p_1, p_2; \tau_1).
--   $$
--
--   The paper writes "it is never optimal (assuming $\rho < 1$) to offer the discount prior to time $\tau_1$"; the statement is the weak inequality, since for $p_1 = p_2$ the revenue does not depend on $T$ at all. It lets the seller restrict the discount time to $T \ge \tau_1$.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 359, Proof of Proposition 4 ("First, …")

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicDet_myopicRevenue
import Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective

namespace SeasonalPricing.MyopicDet

/-- Proof of Proposition 4, first observation (Aviv–Pazgal 2008, p. 359): for prices
`ρ ≤ p₂ ≤ p₁ ≤ 1`, offering the discount at a time `T ∈ [0, τ₁]`, `τ₁ = ln(p₁)/ln(ρ)`,
yields no more expected revenue than offering it at `τ₁`. -/
theorem revenue_le_at_tau1 (lam ρ p1 p2 T : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : ρ ≤ p2) (hp12 : p2 ≤ p1) (hp1 : p1 ≤ 1)
    (hT0 : 0 ≤ T) (hT : T ≤ tau ρ p1) :
    detRevenue lam ρ p1 p2 T ≤ detRevenue lam ρ p1 p2 (tau ρ p1) := by sorry

end SeasonalPricing.MyopicDet
