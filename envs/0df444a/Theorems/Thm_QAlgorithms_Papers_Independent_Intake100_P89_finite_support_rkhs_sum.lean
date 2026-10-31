-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_finite_support_rkhs_sum
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.finite_support_rkhs_sum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:50:41.493593+00:00
-- url     : https://prove2.me/theorems/d6c075c0-92db-4411-bac5-d9c19842ffaf
-- title:
--   §9, finite-dimensional support corollary
-- statement:
--   Let $V,W$ be independent Borel centered jointly Gaussian elements of a real separable Banach space with disjoint closed support subspaces. If at least one support is finite dimensional, a continuous projection separates the two supports, after interchanging their roles if necessary. Consequently
--   $$H_{V+W}=H_V\oplus H_W,\qquad\|h_V+h_W\|_{H_{V+W}}^2=\|h_V\|_{H_V}^2+\|h_W\|_{H_W}^2.$$
--   The finite-dimensional condition is on an ambient support, and the complementary subspace contains the other support.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 19, §9, finite-dimensional support corollary

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section MoreResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- §9, finite-dimensional support corollary, arXiv:0805.3252v1, PDF p.19.
If only the second support is finite dimensional, swap V and W: the text does not justify complementation of an arbitrary infinite-dimensional first support. -/
theorem finite_support_rkhs_sum
{B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [TopologicalSpace.SeparableSpace B]
    (V W : Omega → B) (hV : BorelCenteredGaussianElement P V) (hW : BorelCenteredGaussianElement P W)
    (hjoint : BorelCenteredGaussianElement P (fun o => (V o, W o)))
    (hind : Indep (MeasurableSpace.comap V (borel B))
      (MeasurableSpace.comap W (borel B)) P)
    (hdisjoint : Disjoint (supportSpace P V) (supportSpace P W))
    (hfinite : FiniteDimensional ℝ (supportSpace P V) ∨
      FiniteDimensional ℝ (supportSpace P W)) :
    (SupportProjection P V W ∨ SupportProjection P W V) ∧ RKHSSum P V W := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
