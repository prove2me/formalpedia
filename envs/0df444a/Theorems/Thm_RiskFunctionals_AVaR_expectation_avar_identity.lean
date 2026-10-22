-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_expectation_avar_identity
-- name    : RiskFunctionals.AVaR.expectation_avar_identity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:18.671923+00:00
-- url     : https://prove2.me/theorems/0882ce58-2440-4b5d-8b29-d4f6e196940c
-- title:
--   (2.17) — $\mathbb E Y=\alpha\,\mathbb{AV@R}_\alpha(Y)-(1-\alpha)\,\mathbb{AV@R}_{1-\alpha}(-Y)$
-- statement:
--   Let $Y$ be an integrable random variable and $0<\alpha<1$. Then
--   $$\mathbb E Y = \alpha\,\mathbb{AV@R}_\alpha(Y) - (1-\alpha)\,\mathbb{AV@R}_{1-\alpha}(-Y). \tag{2.17}$$
--
--   The identity splits the mean into the average of the lower $\alpha$-tail of $Y$ and the average of the upper $(1-\alpha)$-tail, the latter written through the lower tail of $-Y$.
--
--   **Formalization Note** $\mathbb{AV@R}_\alpha$ is the book's lower-tail functional (2.15), applied to $Y$ and to $-Y$. $Y$ is assumed measurable and integrable.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 48, Eq. (2.17)

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- Pflug & Römisch, p. 48, (2.17): for integrable `Y` and `α ∈ (0, 1)`,
`𝔼Y = α 𝔸𝕍@ℝ_α(Y) − (1 − α) 𝔸𝕍@ℝ_{1−α}(−Y)`. -/
theorem expectation_avar_identity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y) (hYi : Integrable Y P) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∫ ω, Y ω ∂P = α * averageValueAtRisk P Y α
      - (1 - α) * averageValueAtRisk P (fun ω => -Y ω) (1 - α) := by sorry

end RiskFunctionals.AVaR
