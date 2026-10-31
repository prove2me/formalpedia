-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_independent_rkhs_sum
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.independent_rkhs_sum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:49:56.407691+00:00
-- url     : https://prove2.me/theorems/d13d7bf7-282e-49d4-a684-37d919693436
-- title:
--   Lemma 9.1: independent sum with complemented disjoint supports
-- statement:
--   Let $V,W$ be independent Borel centered jointly Gaussian elements of a real separable Banach space. Suppose their closed support subspaces have trivial intersection, and the support of $V$ has a closed linear complement containing the support of $W$. Then
--   $$H_{V+W}=H_V\oplus H_W,\qquad\|h_V+h_W\|_{H_{V+W}}^2=\|h_V\|_{H_V}^2+\|h_W\|_{H_W}^2.$$
--   The decomposition is unique. Complementation is encoded by a continuous projection onto the first support that vanishes on the second.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 18, Lemma 9.1: independent sum with complemented disjoint supports

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

/-- Lemma 9.1: independent sum with complemented disjoint supports, arXiv:0805.3252v1, PDF p.18.
Disjointness concerns the closed supports, and the complement hypothesis is not inferred from stochastic independence. -/
theorem independent_rkhs_sum
{B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [TopologicalSpace.SeparableSpace B]
    (V W : Omega → B) (hV : BorelCenteredGaussianElement P V) (hW : BorelCenteredGaussianElement P W)
    (hjoint : BorelCenteredGaussianElement P (fun o => (V o, W o)))
    (hind : Indep (MeasurableSpace.comap V (borel B))
      (MeasurableSpace.comap W (borel B)) P)
    (hdisjoint : Disjoint (supportSpace P V) (supportSpace P W))
    (hcomplement : SupportProjection P V W) : RKHSSum P V W := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
