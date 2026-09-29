-- Prove2me | Theorems.Thm_SeasonalPricing_MyopicExp_reduced_revenue
-- name    : SeasonalPricing.MyopicExp.reduced_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:15:48.96249+00:00
-- url     : https://prove2.me/theorems/6cc0b986-7de9-4bbe-a54b-e2919f4579cc
-- title:
--   Proof of Proposition 3 — the reduced problem $p_2\lambda e^{-p_2} + (p_1-p_2)\lambda T e^{-p_1}$
-- statement:
--   Let the base valuations be Gamma with mean $\mu = 1$ and coefficient of variation $c = 1$, i.e. exponential with mean one, so $\bar F(x) = e^{-x}$ for $x \ge 0$. Let the season have length $H = 1$, let $\rho = e^{-\alpha H} = 1$ (valuations do not decline), let customers arrive at rate $\lambda > 0$, let the discount time satisfy $0 < T \le 1$, and let inventory be unlimited. Then for all prices $0 \le p_2 \le p_1$ the expected revenue of the contingent policy with myopic customers equals
--
--   $$
--   p_1 \Lambda_I(p_1) + p_2\big(\Lambda_W(p_1, p_2) + \Lambda_L(p_2)\big) = p_2 \cdot \lambda e^{-p_2} + (p_1 - p_2) \cdot \lambda T e^{-p_1}.
--   $$
--
--   This is the reduction in the paper's proof of Proposition 3: the seller's problem becomes $\pi^*_{C/N} = \max_{p_1, p_2 \le p_1}\{p_2 \lambda e^{-p_2} + (p_1 - p_2)\lambda T e^{-p_1}\}$. The identity evaluates the three segment integrals in closed form.
--
--   **Formalization Note** The paper states the reduced problem without a sign condition; the identity is stated for nonnegative prices, where $\bar F(x) = e^{-x}$ holds at every argument. For negative prices the model's tail equals $1$ and the reduced expression is not the model's revenue; the goal theorem handles all real prices directly. The hypothesis $\rho = 1$ is written `decayRatio α 1 = 1` together with $\alpha \ge 0$ (§3).
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 358, Proof of Proposition 3 (the reduced problem)

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicExp_gammaValuationTail
import Definitions.Def_SeasonalPricing_Shared_LambdaI
import Definitions.Def_SeasonalPricing_MyopicExp_contingentMyopicRevenue

namespace SeasonalPricing.MyopicExp

/-- Proof of Proposition 3 (Aviv–Pazgal 2008, p. 358), the reduced problem: with base valuations
Gamma with mean `μ = 1` and coefficient of variation `c = 1` (i.e. exponential with mean one),
`ρ = e^{−αH} = 1`, season length `H = 1`, and unlimited inventory, the expected revenue of the
contingent policy with myopic customers, premium price `p₁` and discount price `p₂`,
`0 ≤ p₂ ≤ p₁`, equals `p₂ · λe^{−p₂} + (p₁ − p₂) · λTe^{−p₁}`. -/
theorem reduced_revenue (lam α T p1 p2 : ℝ) (hlam : 0 < lam) (hT0 : 0 < T) (hT1 : T ≤ 1)
    (hα : 0 ≤ α) (hρ : decayRatio α 1 = 1) (hp2 : 0 ≤ p2) (hp21 : p2 ≤ p1) :
    contingentMyopicRevenue lam α T 1 (gammaValuationTail 1 1) p1 p2 =
      p2 * lam * Real.exp (-p2) + (p1 - p2) * lam * T * Real.exp (-p1) := by sorry

end SeasonalPricing.MyopicExp
