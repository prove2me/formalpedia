-- Prove2me | Theorems.Thm_RiskFunctionals_Distortion_distortion_examples
-- name    : RiskFunctionals.Distortion.distortion_examples
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:56.987546+00:00
-- url     : https://prove2.me/theorems/14742eee-2084-4895-95d2-3233a6915d20
-- title:
--   Examples 2.63 — $H(p)=p$, $\mathbb 1_{[\alpha,1]}$, $\min(p/\alpha,1)$ give $\mathbb E$, $\mathbb{V@R}_\alpha$, $\mathbb{AV@R}_\alpha$
-- statement:
--   Let $G$ be a distribution function on $\mathbb R$ (the law of a random variable $Y$), with quantile function $G^{-1}$, and let $\mathcal A_H\{G\}=\int_0^1G^{-1}(p)\,dH(p)$ be the distortion functional of an increasing right continuous $H$ on $[0,1]$.
--
--   1. If $Y$ is integrable and $H(p)=p$ on $[0,1]$, then $\mathcal A_H\{G\}$ is the expectation:
--   $$\mathcal A_H\{G\}=\mathbb E(Y)=\int_0^1G^{-1}(p)\,dp=-\int_{-\infty}^0G(u)\,du+\int_0^\infty(1-G(u))\,du.$$
--   2. If $0<\alpha\le1$ and $H(p)=\mathbb 1_{[\alpha,1]}(p)$ on $[0,1]$, then $\mathcal A_H\{G\}$ is the value-at-risk, $\mathbb{V@R}_\alpha(Y)=G^{-1}(\alpha)$.
--   3. If $0<\alpha\le1$ and $H(p)=\min(p/\alpha,1)$ on $[0,1]$, then $\mathcal A_H\{G\}$ is the average value-at-risk,
--   $$\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G^{-1}(p)\,dp.$$
--
--   These are the three basic members of the class of distortion functionals; the third family generates all concave distortions through the Choquet representation.
--
--   **Formalization Note** Each $H$ is any Mathlib `StieltjesFunction` with the printed values on $[0,1]$; the functional integrates over $(0,1]$. The book states the examples without a range for $\alpha$; $0<\alpha\le1$ is the range of $\mathbb{AV@R}_\alpha$ (Definition 2.33). Integrability of $Y$ is assumed in part 1 only, where the expectation is written; at $\alpha=1$ in part 2 with $G<1$ everywhere both sides are the junk value $0$ (the book's $+\infty$).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 82–83, Examples 2.63

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional

namespace RiskFunctionals.Distortion

open MeasureTheory

/-- Examples 2.63 (Pflug & Römisch, pp. 82–83), the first three bullets, for a distribution `G`
(law `μ`, a probability measure on `ℝ`):
(i) `H(p) = p` gives the expectation,
  `𝔼(Y) = ∫₀¹ G⁻¹(p) dp = −∫_{−∞}^0 G(u) du + ∫_0^∞ (1 − G(u)) du` (for integrable `Y`);
(ii) `H(p) = 𝟙_{[α,1]}(p)` gives the value-at-risk `𝕍@ℝ_α(Y) = G⁻¹(α)`;
(iii) `H(p) = min(p/α, 1)` gives the average value-at-risk `𝔸𝕍@ℝ_α(Y) = (1/α) ∫₀^α G⁻¹(p) dp`.
In (ii) and (iii) `0 < α ≤ 1`. Each `H` is any Stieltjes function with the printed values on
`[0, 1]`. -/
theorem distortion_examples (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    -- (i) H(p) = p: the expectation
    (Integrable (fun x : ℝ => x) μ → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = p) →
        distortionFunctional H μ = ∫ x, x ∂μ ∧
        ∫ x, x ∂μ = ∫ p in Set.Ioc (0 : ℝ) 1, quantileFunction μ p ∧
        ∫ x, x ∂μ = -(∫ u in Set.Iic (0 : ℝ), distributionFunction μ u) +
          ∫ u in Set.Ioi (0 : ℝ), (1 - distributionFunction μ u)) ∧
    -- (ii) H(p) = 𝟙_{[α,1]}(p): the value-at-risk
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = if α ≤ p then 1 else 0) →
        distortionFunctional H μ = quantileFunction μ α) ∧
    -- (iii) H(p) = min(p/α, 1): the average value-at-risk
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ H : StieltjesFunction ℝ,
      (∀ p ∈ Set.Icc (0 : ℝ) 1, H p = min (p / α) 1) →
        distortionFunctional H μ = averageValueAtRisk μ α) := by sorry

end RiskFunctionals.Distortion
