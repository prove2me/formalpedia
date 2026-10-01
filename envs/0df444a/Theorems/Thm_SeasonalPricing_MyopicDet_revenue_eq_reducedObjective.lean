-- Prove2me | Theorems.Thm_SeasonalPricing_MyopicDet_revenue_eq_reducedObjective
-- name    : SeasonalPricing.MyopicDet.revenue_eq_reducedObjective
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:01:58.908734+00:00
-- url     : https://prove2.me/theorems/01dc4c10-f2ec-4921-8066-75af28e22b43
-- title:
--   Proof of Proposition 4, third observation — on $[\tau_1, \tau_2]$ the revenue is $\lambda G(p_1, p_2)$
-- statement:
--   Let $\lambda > 0$ and $0 < \rho < 1$, and consider myopic customers with identical base valuation $1$, valuation $\rho^t$ at time $t$, season $[0, 1]$ and unlimited inventory, with expected revenue $R_\rho(p_1, p_2; T)$. Let $\rho \le p_2 \le p_1 \le 1$, $\tau_1 = \ln(p_1)/\ln(\rho)$ and $\tau_2 = \ln(p_2)/\ln(\rho)$. Then for every discount time $T \in [\tau_1, \tau_2]$,
--
--   $$
--   R_\rho(p_1, p_2; T) = \lambda\left[(p_1 - p_2)\cdot\frac{\ln p_1}{\ln\rho} + p_2\cdot\frac{\ln p_2}{\ln\rho}\right].
--   $$
--
--   In particular the revenue does not depend on where in $[\tau_1, \tau_2]$ the discount is offered. Together with the first two observations this reduces the seller's problem over prices and discount time to the maximization of the bracket over $\rho \le p_2 \le p_1 \le 1$.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 359, Proof of Proposition 4 ("Third, …")

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicDet_myopicRevenue
import Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective

namespace SeasonalPricing.MyopicDet

/-- Proof of Proposition 4, third observation (Aviv–Pazgal 2008, p. 359): for prices
`ρ ≤ p₂ ≤ p₁ ≤ 1` and any discount time `T ∈ [τ₁, τ₂]`, the expected revenue equals
`λ · [(p₁ − p₂) · ln(p₁)/ln(ρ) + p₂ · ln(p₂)/ln(ρ)]`, independently of `T`. -/
theorem revenue_eq_reducedObjective (lam ρ p1 p2 T : ℝ) (hlam : 0 < lam) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hp2 : ρ ≤ p2) (hp12 : p2 ≤ p1) (hp1 : p1 ≤ 1)
    (hT1 : tau ρ p1 ≤ T) (hT2 : T ≤ tau ρ p2) :
    detRevenue lam ρ p1 p2 T = lam * reducedObjective ρ p1 p2 := by sorry

end SeasonalPricing.MyopicDet
