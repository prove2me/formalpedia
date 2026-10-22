-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_alpha_bounds_tail_probs
-- name    : RiskFunctionals.AVaR.alpha_bounds_tail_probs
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:09.001009+00:00
-- url     : https://prove2.me/theorems/624eea7e-7a89-4e24-bcac-9eb941e1d437
-- title:
--   p. 49 and (2.18) — $\alpha^-_G\le\alpha\le\alpha^+_G$, $\mathbb P\{Y\le G^{-1}(\alpha)\}=\alpha^+_G$, $\mathbb P\{Y<G^{-1}(\alpha)\}=\alpha^-_G$
-- statement:
--   Let $Y$ be a random variable with distribution function $G$ and quantile function $G^{-1}$, let $0<\alpha\le1$, and suppose $G^{-1}(\alpha)$ is finite. Let
--   $$\alpha^+_G = \inf\{G(u) : G(u)\ge\alpha\},\qquad \alpha^-_G = \sup\{G(u) : G(u)<\alpha\}.$$
--   Then
--   1. $\alpha^+_G = G(G^{-1}(\alpha))$;
--   2. $\alpha^-_G = G(G^{-1}(\alpha)-) = \lim_{h\downarrow 0} G(G^{-1}(\alpha)-h)$;
--   3. $\alpha^-_G\le\alpha\le\alpha^+_G$;
--   4. $$\mathbb P\{Y\le G^{-1}(\alpha)\} = \alpha^+_G,\qquad \mathbb P\{Y< G^{-1}(\alpha)\} = \alpha^-_G. \tag{2.18}$$
--
--   The two quantities differ exactly when $G$ jumps at $G^{-1}(\alpha)$; they are the weights in the conditional tail expectation representations of the average value-at-risk.
--
--   **Formalization Note** "$G^{-1}(\alpha)$ finite" is the hypothesis that $G(u)\ge\alpha$ for some $u$; it is automatic for $\alpha<1$ and excludes only $\alpha=1$ with $G<1$ everywhere, where the book's $G^{-1}(1)=+\infty$ and the identities are not meaningful as real numbers. The left limit is a limit as $h\to0$ with $h>0$. $Y$ is assumed measurable.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 49, Eq. (2.18)

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk

namespace RiskFunctionals.AVaR

open MeasureTheory Filter Topology

/-- Pflug & Römisch, p. 49, the quantities `α⁺_G`, `α⁻_G` and (2.18): for an integrable `Y`
with distribution function `G` and `0 < α ≤ 1` with `G⁻¹(α)` finite,
`α⁺_G = G(G⁻¹(α))`, `α⁻_G = G(G⁻¹(α)−) = lim_{h↓0} G(G⁻¹(α) − h)`, `α⁻_G ≤ α ≤ α⁺_G`,
`ℙ{Y ≤ G⁻¹(α)} = α⁺_G` and `ℙ{Y < G⁻¹(α)} = α⁻_G`. -/
theorem alpha_bounds_tail_probs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (α : ℝ) (hα₀ : 0 < α)
    (hα₁ : α ≤ 1) (hfin : ∃ u : ℝ, α ≤ distributionFunction (P.map Y) u) :
    alphaPlus (P.map Y) α =
        distributionFunction (P.map Y) (quantileFunction (P.map Y) α) ∧
    Tendsto (fun h : ℝ => distributionFunction (P.map Y) (quantileFunction (P.map Y) α - h))
        (𝓝[>] 0) (𝓝 (alphaMinus (P.map Y) α)) ∧
    alphaMinus (P.map Y) α ≤ α ∧ α ≤ alphaPlus (P.map Y) α ∧
    P.real {ω | Y ω ≤ quantileFunction (P.map Y) α} = alphaPlus (P.map Y) α ∧
    P.real {ω | Y ω < quantileFunction (P.map Y) α} = alphaMinus (P.map Y) α := by sorry

end RiskFunctionals.AVaR
