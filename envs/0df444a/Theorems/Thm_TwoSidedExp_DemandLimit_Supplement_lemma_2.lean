-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_Supplement_lemma_2
-- name    : TwoSidedExp.DemandLimit.Supplement.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:22:22.711423+00:00
-- url     : https://prove2.me/theorems/95147358-5a8d-4e77-9aaa-85f756901844
-- title:
--   Lemma 2 (supports Theorem 2) — expectation ratio bound
-- statement:
--   Let X and Z be nonnegative integrable real random variables on a probability space with law μ, and write μ_X = E_μX and μ_Z = E_μZ. For every ϵ > 0,
--
--   $$\left|\mathbb E_\mu\frac{X}{\epsilon+X+Z}-\frac{\mu_X}{\epsilon+\mu_X+\mu_Z}\right|\le\frac{(\epsilon+\mu_Z)\mathbb E_\mu|X-\mu_X|+\mu_X\mathbb E_\mu|Z-\mu_Z|}{\epsilon^2}.$$
--
--   No independence assumption is needed. This controls replacement of random consideration counts by their means.
--
--   **Formalization Note** Nonnegativity holds almost surely. Having finite means is expressed by integrability; these hypotheses also make the bounded ratio and absolute deviations integrable.
--
--   Differences from the source:
--   - reading: X and Z are nonnegative random variables with means. → X and Z are integrable and nonnegative almost surely on a probability space.; reason: Finite means and the probability-space convention make the displayed expectations well-defined; null-set changes do not affect them.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, p. A4 (PDF 40), Lemma 2

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

/-- Lemma 2, p. A4: having means means integrability on a probability space. -/
theorem lemma_2 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Z : Ω → ℝ) (hX : Integrable X μ) (hZ : Integrable Z μ)
    (hXpos : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hZpos : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (eps : ℝ) (heps : 0 < eps) :
    |(∫ ω, X ω / (eps + X ω + Z ω) ∂μ) -
        (∫ ω, X ω ∂μ) / (eps + (∫ ω, X ω ∂μ) + (∫ ω, Z ω ∂μ))| ≤
      ((eps + (∫ ω, Z ω ∂μ)) * (∫ ω, |X ω - (∫ ω, X ω ∂μ)| ∂μ) +
        (∫ ω, X ω ∂μ) * (∫ ω, |Z ω - (∫ ω, Z ω ∂μ)| ∂μ)) / eps ^ 2 := by sorry

end TwoSidedExp.DemandLimit.Supplement
