-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_avar_deviation_min
-- name    : RiskFunctionals.AVaR.avar_deviation_min
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:14.652989+00:00
-- url     : https://prove2.me/theorems/23ac7a07-051b-46bf-bb21-c0f205a82def
-- title:
--   Proposition 2.74 — $\mathbb{AV@R}\mathbb D_\alpha(Y)=\min_a\{\mathbb E([Y-a]^+)+\frac{1-\alpha}{\alpha}\mathbb E([Y-a]^-)\}$
-- statement:
--   Let $Y$ be an integrable random variable with distribution function $G$, let $0<\alpha\le1$, and write $[y]^+=\max(y,0)$, $[y]^-=-\min(y,0)$. Then the minimum
--   $$\min\Big\{\mathbb E\big([Y-a]^+\big) + \frac{1-\alpha}{\alpha}\,\mathbb E\big([Y-a]^-\big) : a\in\mathbb R\Big\} \tag{2.112}$$
--   is attained, and its value is the average value-at-risk deviation
--   $$\mathbb{AV@R}\mathbb D_\alpha(Y) = \mathbb E(Y) - \mathbb{AV@R}_\alpha(Y).$$
--
--   The average value-at-risk deviation is therefore the minimal-loss deviation functional for the piecewise linear loss $h(v)=[v]^+ + \frac{1-\alpha}{\alpha}[v]^-$.
--
--   **Formalization Note** The statement is as printed, for every $0<\alpha\le1$, and "min" is read as an attained minimum. At $\alpha=1$ with $Y$ not essentially bounded above the minimum is not attained (FINDINGS F3); the variant `RiskFunctionals.AVaR.avar_deviation_min_corrected` states the result under the hypothesis that $G^{-1}(\alpha)$ is finite. The book refers to "Definition 2.16" for the deviation; it means Eq. (2.16). $Y$ is assumed measurable.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 109, Proposition 2.74

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- Proposition 2.74 (Pflug & Römisch, p. 109): for integrable `Y` and `0 < α ≤ 1`, the minimum
`min {𝔼([Y − a]⁺) + ((1 − α)/α) 𝔼([Y − a]⁻) : a ∈ ℝ}` (2.112) is attained and equals the
average value-at-risk deviation `𝔸𝕍@ℝ𝔻_α(Y) = 𝔼(Y) − 𝔸𝕍@ℝ_α(Y)`. Here `[y]⁺ = max(y, 0)`,
`[y]⁻ = −min(y, 0)`. Stated as printed, for every `0 < α ≤ 1` (see finding F3 on `α = 1`). -/
theorem avar_deviation_min {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    IsLeast {v : ℝ | ∃ a : ℝ, v = ∫ ω, max (Y ω - a) 0 ∂P
        + (1 - α) / α * ∫ ω, -min (Y ω - a) 0 ∂P}
      (avarDeviation P Y α) := by sorry

end RiskFunctionals.AVaR
