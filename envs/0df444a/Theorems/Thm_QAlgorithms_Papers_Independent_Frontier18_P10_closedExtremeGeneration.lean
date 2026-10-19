-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_closedExtremeGeneration
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.closedExtremeGeneration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:06:41.391285+00:00
-- url     : https://prove2.me/theorems/f3caefa8-4af7-487b-9747-03505a81a1c7
-- title:
--   Proposition 5: closed-extreme barycentric generation
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   If $A$ is convex and pointwise $\mu$-compact, then
--   $$\overline{\operatorname{co}}(\operatorname{extr}A)=A,
--   \qquad b\bigl(M(\overline{\operatorname{extr}A})\bigr)=A.$$
--
--
--   This gives closed-extreme barycentric generation by general probability measures.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 7, Proposition 5: closed-extreme barycentric generation

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LocallyConvexResults

variable {E : Type u} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [hgroup : IsUniformAddGroup E] [hsmul : ContinuousSMul ℝ E]
    [hlc : LocallyConvexSpace ℝ E] [hhaus : T2Space E]

include hgroup hsmul hlc hhaus

/-- Proposition 5, PDF pp.7–8: both overbars are essential. No countable
atomic extreme-point generation is asserted. -/
theorem closedExtremeGeneration (A : Set E) (hA : GeneralBarycenterSpace A)
    (hc : Convex ℝ A) (hm : PointwiseMuCompact A) :
    closedConvexHull ℝ (A.extremePoints ℝ) = A ∧
    Set.range (pettisBarycenter (closure (A.extremePoints ℝ))) = A := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
