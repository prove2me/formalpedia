-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_pettisExpectation_exists
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.pettisExpectation_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:33:11.625459+00:00
-- url     : https://prove2.me/theorems/3d18e39e-00f5-402c-99b2-a04ab9f1b7ad
-- title:
--   Lemma 2.1: existence of the Pettis expectation
-- statement:
--   Let $X$ be a Borel measurable map from a probability space into a real separable Banach space $B$, with $E\|X\|<\infty$. Then an element $b\in B$ exists such that
--   $$\ell(b)=E[\ell(X)]\quad\text{for every }\ell\in B^*.$$
--   This is existence of the Pettis expectation; Gaussianity and centeredness are unnecessary.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 4, Lemma 2.1: existence of the Pettis expectation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section BanachResults

variable {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]

variable [hComplete : CompleteSpace B] [hSeparable : TopologicalSpace.SeparableSpace B]

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP hComplete hSeparable

/-- Lemma 2.1: existence of the Pettis expectation, arXiv:0805.3252v1, PDF p.4.
Mathlib Bochner integration and ContinuousLinearMap.integral_comp_comm supply the substrate; this is a new existential corollary, not verbatim reuse. -/
theorem pettisExpectation_exists
(X : Omega → B) (hX : @Measurable Omega B _ (borel B) X)
    (hfinite : (∫⁻ o, ENNReal.ofReal ‖X o‖ ∂P) < ∞) :
    ∃ b : B, ∀ l : B →L[ℝ] ℝ, Integrable (fun o => l (X o)) P ∧
      l b = ∫ o, l (X o) ∂P := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
