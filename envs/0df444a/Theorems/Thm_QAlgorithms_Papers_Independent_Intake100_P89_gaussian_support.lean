-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_gaussian_support
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.gaussian_support
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:44:25.89015+00:00
-- url     : https://prove2.me/theorems/27e00847-97f5-42ef-9aa7-37dd9dd1660d
-- title:
--   Lemma 5.1: support equals ambient RKHS closure
-- statement:
--   For a Borel centered Gaussian element $W$ of a real separable Banach space $B$, its support is both the ambient closure of the RKHS and the ambient closure of the covariance range:
--   $$\operatorname{supp}(P^W)=\overline H^{\,B}=\overline{S(B^*)}^{\,B}.$$
--   Support means that every ambient open ball about the point has positive probability; this also covers the zero Gaussian.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 14, Lemma 5.1: support equals ambient RKHS closure

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

/-- Lemma 5.1: support equals ambient RKHS closure, arXiv:0805.3252v1, PDF p.14.
For W=0 all three sets are {0}. -/
theorem gaussian_support
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    supportSet P W = closure (banachRKHS P W) ∧
      supportSet P W = closure (Set.range (covarianceMap P W)) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
