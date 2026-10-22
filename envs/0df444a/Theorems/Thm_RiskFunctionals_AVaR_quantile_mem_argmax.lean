-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_quantile_mem_argmax
-- name    : RiskFunctionals.AVaR.quantile_mem_argmax
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:58.348377+00:00
-- url     : https://prove2.me/theorems/d3918779-fe82-45e0-8bcd-ef468d1b8380
-- title:
--   (2.24) — $G^{-1}(\alpha)$ maximizes $x\mapsto x-\frac1\alpha\mathbb E([Y-x]^-)$
-- statement:
--   Let $Y$ be an integrable random variable with distribution function $G$ and quantile function $G^{-1}$, let $0<\alpha\le1$, suppose $G^{-1}(\alpha)$ is finite, and write $[y]^- = -\min(y,0)$. Then
--   $$G^{-1}(\alpha) \in \operatorname{argmax}\Big\{x - \frac1\alpha\,\mathbb E\big([Y-x]^-\big) : x\in\mathbb R\Big\}, \tag{2.24}$$
--   that is, for every real $x$,
--   $$x - \frac1\alpha\,\mathbb E\big([Y-x]^-\big) \le G^{-1}(\alpha) - \frac1\alpha\,\mathbb E\big([Y-G^{-1}(\alpha)]^-\big).$$
--
--   This is the fact on which the Rockafellar–Uryasev representation of the average value-at-risk rests: the maximizing threshold is the $\alpha$-quantile.
--
--   **Formalization Note** "$G^{-1}(\alpha)$ finite" is the hypothesis that $G(u)\ge\alpha$ for some $u$; it is automatic for $\alpha<1$. $Y$ is assumed measurable and integrable, so every expectation in the statement is finite.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 50, proof of Theorem 2.34, Eq. (2.24)

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- Pflug & Römisch, p. 50, (2.24): `G⁻¹(α) ∈ argmax {x − (1/α) 𝔼([Y − x]⁻) : x ∈ ℝ}`, where
`[y]⁻ = −min(y, 0)`. Stated for integrable `Y`, `0 < α ≤ 1`, and `G⁻¹(α)` finite (automatic
for `α < 1`). -/
theorem quantile_mem_argmax {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hfin : ∃ u : ℝ, α ≤ distributionFunction (P.map Y) u) :
    ∀ x : ℝ, x - (1 / α) * ∫ ω, -min (Y ω - x) 0 ∂P ≤
      quantileFunction (P.map Y) α
        - (1 / α) * ∫ ω, -min (Y ω - quantileFunction (P.map Y) α) 0 ∂P := by sorry

end RiskFunctionals.AVaR
