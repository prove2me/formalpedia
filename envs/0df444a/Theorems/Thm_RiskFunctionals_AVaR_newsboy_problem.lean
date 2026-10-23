-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_newsboy_problem
-- name    : RiskFunctionals.AVaR.newsboy_problem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:05.532211+00:00
-- url     : https://prove2.me/theorems/73e5e6bf-5f40-4518-b905-9581710a28a7
-- title:
--   Example 2.40 — the newsboy problem: maximal expected profit $(s-b)\,\mathbb{AV@R}_\alpha(Y)$ with $\alpha=\frac{s-b}{s-r}$
-- statement:
--   A newsboy buys $x$ copies of a newspaper at a price $b$ each, sells them at a price $s>b$, and returns unsold copies for a refund $r<b$. The demand is an integrable random variable $Y$. With $[y]^-=-\min(y,0)$, the profit of the order size $x\in\mathbb R$ is
--   $$H(x,Y) = s\min(x,Y) + r[Y-x]^- - bx = (s-b)x - (s-r)[Y-x]^-.$$
--   Let $G$ be the distribution function of $Y$ and
--   $$\alpha = \frac{s-b}{s-r}.$$
--   Then the expected profit $\mathbb E[H(x,Y)]$, over $x\in\mathbb R$, takes the maximal value
--   $$(s-b)\,\mathbb{AV@R}_\alpha(Y),$$
--   and the order size $x^*=G^{-1}(\alpha)$ is optimal: $\mathbb E[H(x^*,Y)]=(s-b)\,\mathbb{AV@R}_\alpha(Y)$.
--
--   The newsboy problem is the classical single-period inventory model; the example identifies its optimal value with a scaled average value-at-risk of the demand and its optimal order with the critical-fractile quantile.
--
--   **Formalization Note** The three claims are stated together: the algebraic identity of the two expressions of $H$ (pointwise), the maximal value (the maximum over all real $x$ is attained and equals $(s-b)\mathbb{AV@R}_\alpha(Y)$), and the optimality of $G^{-1}(\alpha)$. Because $r<b<s$, $0<\alpha<1$, so $G^{-1}(\alpha)$ is finite. "The optimal order size is $x^*$" is read as "$x^*$ attains the maximum"; uniqueness is not claimed (the maximizers form the interval of $\alpha$-quantiles). $Y$ is assumed measurable and integrable; it need not be nonnegative.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 56, Example 2.40

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- Example 2.40 (Pflug & Römisch, p. 56), the newsboy problem: copies are bought at price `b`,
sold at `s > b`, unsold copies refunded at `r < b`; the demand `Y` is an integrable random
variable. The profit of order size `x` is
`H(x, Y) = s min(x, Y) + r [Y − x]⁻ − b x = (s − b) x − (s − r) [Y − x]⁻`, `[y]⁻ = −min(y, 0)`.
With `α = (s − b)/(s − r)`, the expected profit `𝔼[H(x, Y)]` over `x ∈ ℝ` takes the maximal
value `(s − b) 𝔸𝕍@ℝ_α(Y)`, and the order size `x* = G⁻¹(α)` attains it. -/
theorem newsboy_problem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P)
    (b s r : ℝ) (hsb : b < s) (hrb : r < b) :
    (∀ x : ℝ, ∀ ω : Ω, s * min x (Y ω) + r * (-min (Y ω - x) 0) - b * x =
        (s - b) * x - (s - r) * (-min (Y ω - x) 0)) ∧
    IsGreatest
      {v : ℝ | ∃ x : ℝ, v = ∫ ω, (s * min x (Y ω) + r * (-min (Y ω - x) 0) - b * x) ∂P}
      ((s - b) * averageValueAtRisk P Y ((s - b) / (s - r))) ∧
    ∫ ω, (s * min (quantileFunction (P.map Y) ((s - b) / (s - r))) (Y ω)
        + r * (-min (Y ω - quantileFunction (P.map Y) ((s - b) / (s - r))) 0)
        - b * quantileFunction (P.map Y) ((s - b) / (s - r))) ∂P =
      (s - b) * averageValueAtRisk P Y ((s - b) / (s - r)) := by sorry

end RiskFunctionals.AVaR
