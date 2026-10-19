-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_continuousBoundedClosedHull
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.continuousBoundedClosedHull
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:08:11.65137+00:00
-- url     : https://prove2.me/theorems/2efaf247-9899-4ed7-ac59-abbcfb149295
-- title:
--   Corollary 2: convex hull is closed for bounded continuous functions
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   For convex $\mu$-compact $A$ and bounded continuous real $f$, the convex hull is lower semicontinuous, and
--   $$\operatorname{co}f(x)=\inf\left\{\sum_{i=1}^n\lambda_i f(x_i):\lambda_i\ge0,\ \sum_i\lambda_i=1,\ x_i\in A,\ \sum_i\lambda_i x_i=x\right\}
--   =\overline{\operatorname{co}}f(x)\quad(x\in A).$$
--
--
--   This identifies the finite-support infimum with the closed envelope, without asserting attainment or continuity.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 8, Corollary 2: convex hull is closed for bounded continuous functions

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

/-- Corollary 2, PDF p.8: finite-support infimum and coincidence of the
convex hull with the closed convex hull. No finite optimizer or continuity is asserted. -/
theorem continuousBoundedClosedHull (A : Set E) (hA : GeneralBarycenterSpace A)
    (hc : Convex ℝ A) (hm : MuCompact A) (f : E → ℝ)
    (hf : BoundedContinuousOn A f) :
    LowerSemicontinuous (fun x : A =>
      convexHullFunction A (fun y => (f y : EReal)) x) ∧
    ∀ x ∈ A,
      convexHullFunction A (fun y => (f y : EReal)) x =
        (⨅ (e : FiniteEnsemble A) (_ : finiteMean e = x), finiteCost f e) ∧
      convexHullFunction A (fun y => (f y : EReal)) x =
        closedConvexHullFunction A (fun y => (f y : EReal)) x := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
