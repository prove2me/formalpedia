-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_pointwiseObstruction
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.pointwiseObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:08:59.832685+00:00
-- url     : https://prove2.me/theorems/e3bb009c-5266-43cf-8061-5e2d3279a982
-- title:
--   Proposition 7: obstruction from pointwise compactness only
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   If convex $A$ is pointwise $\mu$-compact but is not $\mu$-compact, there is a bounded continuous real $f$ whose convex hull is not lower semicontinuous. For this witness the general-measure representation fails at some point:
--   $$\exists x\in A:\quad \overline{\operatorname{co}}f(x)\ne
--   \inf_{\mu\in M(A):b(\mu)=x}\int_A f\,d\mu.$$
--
--
--   The obstruction requires both the pointwise assumption and failure of full µ-compactness.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 8, Proposition 7: obstruction from pointwise compactness only

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

/-- Proposition 7, PDF pp.8–9: pointwise µ-compactness is required for
this obstruction. The final clause explicitly retains failure of (3). -/
theorem pointwiseObstruction (A : Set E) (hA : GeneralBarycenterSpace A)
    (hc : Convex ℝ A) (hnot : ¬ MuCompact A) (hm : PointwiseMuCompact A) :
    ∃ f : E → ℝ, BoundedContinuousOn A f ∧
      ¬ LowerSemicontinuous (fun x : A =>
        convexHullFunction A (fun y => (f y : EReal)) x) ∧
      ∃ x ∈ A,
        closedConvexHullFunction A (fun y => (f y : EReal)) x ≠
          ⨅ (mu : ProbabilityMeasure A) (_ : pettisBarycenter A mu = x),
            extendedIntegral (mu : Measure A) (fun y : A => (f y : EReal)) := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
