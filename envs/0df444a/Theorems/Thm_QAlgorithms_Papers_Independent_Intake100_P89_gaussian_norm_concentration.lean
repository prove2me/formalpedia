-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_gaussian_norm_concentration
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.gaussian_norm_concentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:46:02.326287+00:00
-- url     : https://prove2.me/theorems/28d66b12-4c9e-4ad4-aacb-9bbaff6fa9e0
-- title:
--   Corollary 5.1: Gaussian norm concentration about its median
-- statement:
--   Let $W$ be a nonzero Borel centered Gaussian element of a real separable Banach space. Write $M(W)$ for the unique median of its norm and $\sigma(W)$ for its weak standard deviation. Then $\sigma(W)>0$ and, for every $x>0$,
--   $$P\{\|W\|-M(W)>x\}\le1-\Phi(x/\sigma(W)).$$
--   Nonzero means that the law is not concentrated at zero; atomlessness of the norm law follows from the Gaussian setting rather than being imposed on an arbitrary law.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 15, Corollary 5.1: Gaussian norm concentration about its median

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

/-- Corollary 5.1: Gaussian norm concentration about its median, arXiv:0805.3252v1, PDF p.15.
The nonzero assumption is carried from the preceding paragraph, PDF p.15; no division by a totalized zero standard deviation. -/
theorem gaussian_norm_concentration
(W : Omega → B) (hW : BorelCenteredGaussianElement P W)
    (hnonzero : ¬ (∀ᵐ o ∂P, W o = 0)) :
    0 < weakSigma P W ∧
    ∀ x : ℝ, 0 < x →
      (P {o | ‖W o‖ - normMedian P W > x}).toReal ≤
        1 - (cdf (gaussianReal 0 1)) (x / weakSigma P W) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
