-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_remark3_stronger_effect_lower_price
-- name    : ReferencePricing.LossAversion.remark3_stronger_effect_lower_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:50:17.29047+00:00
-- url     : https://prove2.me/theorems/25cba3a5-287a-47a1-9a07-a9c3842f0cca
-- title:
--   Remark 3 — a stronger reference effect ($\lambda_1\le\lambda_2$) yields a lower steady-state price, $p^{**}_1\ge p^{**}_2$
-- statement:
--   Consider two loss-neutral problems of the form (2) on the same price set $P=[0,\bar p]$. They share the base demand $d$ (differentiable), the memory $\alpha\in[0,1)$ and the discount factor $\beta\in(0,1)$, and have reference effects $R_1$ and $R_2$, each satisfying Assumptions 1–3. Suppose $R_2$ is "stronger" than $R_1$:
--   $$
--   \lambda_1(r)\le\lambda_2(r)\quad\text{for all } r,
--   $$
--   where $\lambda_i(r)$ is the slope of $R_i(\cdot,r)$ at $0$. If $p^{**}_1$ and $p^{**}_2$ are steady states of the two problems, then
--   $$
--   p^{**}_1\ge p^{**}_2 .
--   $$
--
--   Consumers who are more sensitive to past prices are charged lower prices in the long run. In the loss-averse analysis this orders the steady states of the problems $(P_\theta)$ between those of $(P_L)$ and $(P_G)$.
--
--   **Formalization Note** "If they exist" is the pair of hypotheses that $p^{**}_1$ and $p^{**}_2$ are steady states. The two problems share $\alpha$, as the remark requires ($\alpha_1=\alpha_2$).
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 419, Remark 3 (proof in Appendix A.3, p. 425)

import Mathlib
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_RobustBooking_Shared_Assumptions
open RobustBooking.Shared

namespace ReferencePricing.LossAversion

/-- Remark 3, Popescu and Wu 2007, p. 419: two loss-neutral problems with the same base demand
`d`, memory `α` and discount `β`, and reference effects `R₁`, `R₂` with `λ₁(r) ≤ λ₂(r)`
(`R₂` "stronger"): their steady states, if they exist, satisfy `p**₁ ≥ p**₂`. -/
theorem remark3_stronger_effect_lower_price (pbar α β : ℝ) (d : ℝ → ℝ) (R₁ R₂ : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : Differentiable ℝ d)
    (hA1₁ : Assumption1 pbar d R₁) (hA2₁ : Assumption2 R₁) (hA3₁ : Assumption3 pbar d R₁)
    (hA1₂ : Assumption1 pbar d R₂) (hA2₂ : Assumption2 R₂) (hA3₂ : Assumption3 pbar d R₂)
    (hslope : ∀ r : ℝ, refSlope R₁ r ≤ refSlope R₂ r)
    (p₁ p₂ : ℝ) (hp₁ : IsSteadyState (profit d R₁) α β pbar p₁)
    (hp₂ : IsSteadyState (profit d R₂) α β pbar p₂) :
    p₂ ≤ p₁ := by sorry

end ReferencePricing.LossAversion
