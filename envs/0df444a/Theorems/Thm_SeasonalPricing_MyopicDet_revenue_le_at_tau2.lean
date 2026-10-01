-- Prove2me | Theorems.Thm_SeasonalPricing_MyopicDet_revenue_le_at_tau2
-- name    : SeasonalPricing.MyopicDet.revenue_le_at_tau2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:00:35.450545+00:00
-- url     : https://prove2.me/theorems/a2ddd461-f7e0-496a-bd17-a4f7c7a27068
-- title:
--   Proof of Proposition 4, second observation — a discount after $\tau_2$ is never better than at $\tau_2$
-- statement:
--   Let $\lambda > 0$ and $0 < \rho < 1$, and consider myopic customers with identical base valuation $1$, valuation $\rho^t$ at time $t$, season $[0, 1]$ and unlimited inventory, with expected revenue $R_\rho(p_1, p_2; T)$ for premium price $p_1$, discount price $p_2$ and discount time $T$. Let $\rho \le p_2 \le p_1 \le 1$ and $\tau_2 = \ln(p_2)/\ln(\rho)$. Then for every $T \in [\tau_2, 1]$,
--
--   $$
--   R_\rho(p_1, p_2; T) \le R_\rho(p_1, p_2; \tau_2).
--   $$
--
--   The paper writes "it is never optimal to offer the discounted price after $\tau_2$"; the statement is the weak inequality. It lets the seller restrict the discount time to $T \le \tau_2$.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 359, Proof of Proposition 4 ("Second, …")

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicDet_myopicRevenue
import Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective

namespace SeasonalPricing.MyopicDet

/-- Proof of Proposition 4, second observation (Aviv–Pazgal 2008, p. 359): for prices
`ρ ≤ p₂ ≤ p₁ ≤ 1`, offering the discount at a time `T ∈ [τ₂, 1]`, `τ₂ = ln(p₂)/ln(ρ)`,
yields no more expected revenue than offering it at `τ₂`. -/
theorem revenue_le_at_tau2 (lam ρ p1 p2 T : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hp2 : ρ ≤ p2) (hp12 : p2 ≤ p1) (hp1 : p1 ≤ 1)
    (hT : tau ρ p2 ≤ T) (hT1 : T ≤ 1) :
    detRevenue lam ρ p1 p2 T ≤ detRevenue lam ρ p1 p2 (tau ρ p2) := by sorry

end SeasonalPricing.MyopicDet
