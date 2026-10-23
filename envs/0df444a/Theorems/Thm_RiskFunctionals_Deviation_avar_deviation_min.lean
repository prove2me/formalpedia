-- Prove2me | Theorems.Thm_RiskFunctionals_Deviation_avar_deviation_min
-- name    : RiskFunctionals.Deviation.avar_deviation_min
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:52.64987+00:00
-- url     : https://prove2.me/theorems/cd375330-2116-4ad6-bf2b-b10c5ba5912a
-- title:
--   Proposition 2.74 — $\min\{\mathbb E([Y-a]^+)+\frac{1-\alpha}{\alpha}\mathbb E([Y-a]^-) : a\in\mathbb R\}=\mathbb{AV@R}\mathbb D_\alpha(Y)$
-- statement:
--   Let $Y$ be an integrable random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$ and $0<\alpha\le1$. Write $[y]^+=\max(y,0)$ and $[y]^-=-\min(y,0)$. Then the minimization problem
--   $$\min\Big\{\mathbb E([Y-a]^+)+\frac{1-\alpha}{\alpha}\,\mathbb E([Y-a]^-) : a\in\mathbb R\Big\} \tag{2.112}$$
--   has a solution, and its optimal value is the average value-at-risk deviation
--   $$\mathbb{AV@R}\mathbb D_\alpha(Y)=\mathbb E(Y)-\mathbb{AV@R}_\alpha(Y).$$
--
--   In other words, the minimal loss functional of the piecewise linear loss $h(v)=[v]^++\frac{1-\alpha}{\alpha}[v]^-$ is $\mathbb{AV@R}\mathbb D_\alpha$; this identifies the special case (2.114) of the dual representation of minimal loss functionals.
--
--   **Formalization Note** The minimum is stated as `IsLeast`: the value $\mathbb{AV@R}\mathbb D_\alpha(Y)$ is attained by some $a\in\mathbb R$ and is a lower bound for all others. It is stated, as printed, for every $0<\alpha\le1$; at $\alpha=1$ the objective is $\mathbb E([Y-a]^+)$, whose infimum $0$ is not attained when $Y$ is not essentially bounded above (finding F8), and the variant `RiskFunctionals.Deviation.avar_deviation_min_corrected` adds the hypothesis that makes the minimum exist. $Y$ is assumed measurable. The book's reference "(see Definition 2.16)" is to Eq. (2.16).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 109, Proposition 2.74

import Mathlib
import Definitions.Def_RiskFunctionals_Deviation_AverageValueAtRisk

namespace RiskFunctionals.Deviation

open MeasureTheory

/-- Proposition 2.74 (Pflug & Römisch, p. 109): for integrable `Y` and `0 < α ≤ 1`, the minimum
`min {𝔼([Y − a]⁺) + ((1 − α)/α) 𝔼([Y − a]⁻) : a ∈ ℝ}` (2.112) is attained and equals the
average value-at-risk deviation `𝔸𝕍@ℝ𝔻_α(Y) = 𝔼(Y) − 𝔸𝕍@ℝ_α(Y)`. Here `[y]⁺ = max(y, 0)`,
`[y]⁻ = −min(y, 0)`. Stated as printed, for every `0 < α ≤ 1` (see finding F8 on `α = 1`). -/
theorem avar_deviation_min {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    IsLeast {v : ℝ | ∃ a : ℝ, v = ∫ ω, max (Y ω - a) 0 ∂P
        + (1 - α) / α * ∫ ω, -min (Y ω - a) 0 ∂P}
      (avarDeviation P Y α) := by sorry

end RiskFunctionals.Deviation
