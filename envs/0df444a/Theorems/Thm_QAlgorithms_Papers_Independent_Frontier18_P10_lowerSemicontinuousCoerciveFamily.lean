-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_lowerSemicontinuousCoerciveFamily
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.lowerSemicontinuousCoerciveFamily
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:17:32.750989+00:00
-- url     : https://prove2.me/theorems/c503f0cc-7017-40e5-9618-32cd3cacf721
-- title:
--   Remark 6: lower semicontinuous coercive family under stability
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   If convex $\mu$-compact $A$ satisfies the equivalent conditions of Theorem 1, then there is a family $F$ of nonnegative extended concave lower semicontinuous functions such that
--   $$\overline{\{x\in A:f(x)\le c\}}\text{ is compact}\quad(f\in F,\ c>0),$$
--   and for each compact $K\subseteq A$ some $f\in F$ is bounded above on $K$ by a finite real constant.
--
--   The family may depend on the compact set; no single everywhere-finite coercive function is required.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 15, Remark 6: lower semicontinuous coercive family under stability

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

/-- Remark 6, PDF p.15: under the equivalent stability conditions, the
coercive concave family can be chosen lower semicontinuous. -/
theorem lowerSemicontinuousCoerciveFamily (A : Set E)
    (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A)
    (hm : MuCompact A) (hs : StableConvexSet A) :
    ∃ F : Set (E → ℝ≥0∞), CoerciveConcaveFamily A F ∧
      ∀ f ∈ F, LowerSemicontinuous (fun x : A => f x) := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
