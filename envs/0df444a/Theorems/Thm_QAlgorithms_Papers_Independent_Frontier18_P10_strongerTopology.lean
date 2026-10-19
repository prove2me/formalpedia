-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_strongerTopology
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.strongerTopology
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:11:37.578642+00:00
-- url     : https://prove2.me/theorems/c4d0ea0a-1913-44af-887f-e5b98a1842a5
-- title:
--   Remark 2: strengthening topology on extreme points
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   Assume $A$ is convex and $\mu$-compact. Give its underlying linear space a finer locally convex topology, still satisfying the standing conditions on the closed convex hull. If the old and new topologies agree on $\operatorname{extr}A$, then
--   $$A\text{ is }\mu\text{-compact in the finer topology}.$$
--
--
--   The two ambient realizations are identified by a linear equivalence; the reverse identity is continuous on $A$, and the forward identity on its extreme boundary.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 6, Remark 2: strengthening topology on extreme points

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

/-- Remark 2, PDF p.6: a finer locally convex topology agreeing on the
extreme points preserves µ-compactness. The linear equivalence identifies the
same vector space endowed with the two topologies; its inverse is continuous
on the whole domain, while the forward map is required continuous only on extr A. -/
theorem strongerTopology {F : Type v} [UniformSpace F] [AddCommGroup F]
    [Module ℝ F] [IsUniformAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    (A : Set E) (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A)
    (equiv : E ≃ₗ[ℝ] F) (hB : GeneralBarycenterSpace (equiv '' A))
    (hfiner : ContinuousOn equiv.symm (equiv '' A))
    (hextreme : ContinuousOn equiv (A.extremePoints ℝ))
    (hm : MuCompact A) : MuCompact (equiv '' A) := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
