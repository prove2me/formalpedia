-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_tightnessCriterion
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.tightnessCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:02:55.877251+00:00
-- url     : https://prove2.me/theorems/a82812a5-a5d9-45a4-a3d8-70642c37b64c
-- title:
--   Proposition 1: tightness criterion
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   For convex $A$, $\mu$-compactness is equivalent to the following uniform tightness condition. For every compact $K\subseteq A$ and $\varepsilon>0$, there is a compact $L\subseteq A$ such that every finite or countable decomposition $x=\sum_i\lambda_i x_i$ of any $x\in K$, with $x_i\in A$, $\lambda_i\ge0$ and $\sum_i\lambda_i=1$, satisfies
--   $$\sum_{i:x_i\notin L}\lambda_i<\varepsilon.$$
--   Vector sums are required to converge to $x$.
--
--   This characterizes compact inverse images using uniform control of atomic tails.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 4, Proposition 1: tightness criterion

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

/-- Proposition 1, PDF p.4: strict tail bound, uniformly over all finite or
countable decompositions after the compact set is chosen. -/
theorem tightnessCriterion (A : Set E) (hA : GeneralBarycenterSpace A)
    (hc : Convex ℝ A) : MuCompact A ↔ CountableTightness A := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
