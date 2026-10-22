-- Prove2me | Theorems.Thm_RiskFunctionals_AVaR_ssd_iff_avar_le
-- name    : RiskFunctionals.AVaR.ssd_iff_avar_le
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:10.805885+00:00
-- url     : https://prove2.me/theorems/dcec5648-8ba1-4398-b73c-f463d2d0cd16
-- title:
--   Proposition 2.36 — $Y^{(1)}\prec_{SSD}Y^{(2)}$ iff $\mathbb{AV@R}_\alpha(Y^{(1)})\le\mathbb{AV@R}_\alpha(Y^{(2)})$ for all $\alpha$
-- statement:
--   Let $Y^{(1)}$, $Y^{(2)}$ be integrable random variables. Then
--   $$Y^{(1)} \prec_{SSD} Y^{(2)} \iff \mathbb{AV@R}_\alpha(Y^{(1)}) \le \mathbb{AV@R}_\alpha(Y^{(2)}) \quad\text{for all } 0<\alpha\le1.$$
--
--   The family $(\mathbb{AV@R}_\alpha)_{0<\alpha\le1}$ thus characterizes second-order stochastic dominance completely: the isotonicity of Proposition 2.35(iii) can be inverted.
--
--   **Formalization Note** $\prec_{SSD}$ is defined through nondecreasing concave utilities (Definition 1.10(ii)) and applied to the laws of the two variables. Integrability of both variables is the standing $L_1$ setting in which $\mathbb{AV@R}_\alpha$ is finite; both variables are measurable and live on the same probability space.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 54, Proposition 2.36

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
import Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_AVaR_Orders

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- Proposition 2.36 (Pflug & Römisch, p. 54): for integrable random variables `Y⁽¹⁾`, `Y⁽²⁾`,
`Y⁽¹⁾ ≺_SSD Y⁽²⁾` iff `𝔸𝕍@ℝ_α(Y⁽¹⁾) ≤ 𝔸𝕍@ℝ_α(Y⁽²⁾)` for all `0 < α ≤ 1`. -/
theorem ssd_iff_avar_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y₁ Y₂ : Ω → ℝ) (hY₁ : Measurable Y₁) (hY₁i : Integrable Y₁ P)
    (hY₂ : Measurable Y₂) (hY₂i : Integrable Y₂ P) :
    SSD (P.map Y₁) (P.map Y₂) ↔
      ∀ α ∈ Set.Ioc (0 : ℝ) 1, averageValueAtRisk P Y₁ α ≤ averageValueAtRisk P Y₂ α := by sorry

end RiskFunctionals.AVaR
