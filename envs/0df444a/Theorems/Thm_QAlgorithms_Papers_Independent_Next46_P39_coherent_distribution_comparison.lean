-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_coherent_distribution_comparison
-- name    : QAlgorithms.Papers.Independent.Next46.P39.coherent_distribution_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:54:45.508663+00:00
-- url     : https://prove2.me/theorems/b24f78bb-3b44-43b2-9b3b-c73d936df2d7
-- title:
--   Likelihood and variance comparison of the coherent-state Gaussian laws
-- statement:
--   Fix a true displacement $\alpha\in\mathbb C$. The explicit laws in Eqs.(43),(55) are $p_k(z|\alpha)=k\exp(-k|z-\alpha|^2)$ for $k=2$ (identical) and $k=4$ (conjugate), relative to $d^2z/\pi$. They are normalized and centered, and all the following moments are integrable:
--
--   $$\mathbb E_k|z-\alpha|^2=\frac1k,\qquad \mathbb E_k[\operatorname{Re}(z-\alpha)^2]=\mathbb E_k[\operatorname{Im}(z-\alpha)^2]=\frac1{2k}.$$
--
--   Consequently both complex squared-error variance and either quadrature variance are halved for the conjugate law, while $p_4(\alpha|\alpha)=2p_2(\alpha|\alpha)$. This node compares the printed distributions themselves. The construction and optimality of the oscillator measurements are separate nodes and are deferred here.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 18, §4.3.2, p.18: conjugate versus identical coherent-state sensitivity

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P39

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator Manifold ContDiff

open QAlgorithms.Measurements (DensityPOVM)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixBorel

variable {G I S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype S] [DecidableEq S] [Nonempty S]

variable (R : FiniteModel G I S)

variable {R}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G]

/-- PDF pp.18–19: statistical comparison of the explicit laws (43),(55).
Complex mean squared error and each individual quadrature variance both
fall by a factor two; the likelihood density doubles. -/
theorem coherent_distribution_comparison (a : ℂ) :
    (∀ k ∈ ({2, 4} : Set ℝ),
      Integrable (displacementDensity k a) phaseMeasure ∧
      (∫ z, displacementDensity k a z ∂phaseMeasure) = 1 ∧
      Integrable (fun z => (z - a) * (displacementDensity k a z : ℂ)) phaseMeasure ∧
      (∫ z, (z - a) * (displacementDensity k a z : ℂ) ∂phaseMeasure) = 0 ∧
      Integrable (fun z => Complex.normSq (z - a) * displacementDensity k a z) phaseMeasure ∧
      (∫ z, Complex.normSq (z - a) * displacementDensity k a z ∂phaseMeasure) = k⁻¹ ∧
      Integrable (fun z => (z - a).re ^ 2 * displacementDensity k a z) phaseMeasure ∧
      (∫ z, (z - a).re ^ 2 * displacementDensity k a z ∂phaseMeasure) = (2*k)⁻¹ ∧
      Integrable (fun z => (z - a).im ^ 2 * displacementDensity k a z) phaseMeasure ∧
      (∫ z, (z - a).im ^ 2 * displacementDensity k a z ∂phaseMeasure) = (2*k)⁻¹) ∧
    displacementDensity 4 a a = 2 * displacementDensity 2 a a ∧
    (∫ z, Complex.normSq (z - a) * displacementDensity 4 a z ∂phaseMeasure) =
      (1/2 : ℝ) * ∫ z, Complex.normSq (z - a) * displacementDensity 2 a z ∂phaseMeasure := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
