-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_mixtureAndEnvelopeFormulations
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.mixtureAndEnvelopeFormulations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:16:56.927712+00:00
-- url     : https://prove2.me/theorems/edd2c2f0-223e-41a8-915f-f73d1e8269f6
-- title:
--   Remark 5: mixture openness and envelope formulation
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   For convex $\mu$-compact $A$, openness of midpoint mixing is equivalent to openness of
--   $$A\times A\times[0,1]\longrightarrow A,\qquad(x,y,\lambda)\longmapsto\lambda x+(1-\lambda)y.$$
--   The strong CE-property is equivalent to continuity of $\overline{\operatorname{co}}f$ and equality $\operatorname{co}f=\overline{\operatorname{co}}f$ for every bounded continuous real $f$. The CE-property has the same equivalent formulation restricted to concave $f$.
--
--   The source credits the mixture-map equivalence to Clausing–Papadopoulou [14].
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 15, Remark 5: mixture openness and envelope formulation

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

/-- Remark 5, PDF p.15: mixture openness includes lambda=0 and lambda=1;
the two CE formulations retain both continuity and equality of the envelopes.
The mixture equivalence is credited by the source to Clausing–Papadopoulou [14]. -/
theorem mixtureAndEnvelopeFormulations (A : Set E)
    (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A) (hm : MuCompact A) :
    (StableConvexSet A ↔
      ∀ U : Set (A × A × Set.Icc (0 : ℝ) 1), IsOpen U →
        IsOpen {z : A | ∃ p ∈ U, (z : E) =
          (p.2.2 : ℝ) • (p.1 : E) + (1 - (p.2.2 : ℝ)) • (p.2.1 : E)}) ∧
    (StrongCEProperty A ↔ ∀ f : E → ℝ, BoundedContinuousOn A f →
      Continuous (fun x : A => closedConvexHullFunction A (fun y => (f y : EReal)) x) ∧
      ∀ x ∈ A, convexHullFunction A (fun y => (f y : EReal)) x =
        closedConvexHullFunction A (fun y => (f y : EReal)) x) ∧
    (CEProperty A ↔ ∀ f : E → ℝ, BoundedContinuousOn A f → ConcaveOn ℝ A f →
      Continuous (fun x : A => closedConvexHullFunction A (fun y => (f y : EReal)) x) ∧
      ∀ x ∈ A, convexHullFunction A (fun y => (f y : EReal)) x =
        closedConvexHullFunction A (fun y => (f y : EReal)) x) := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
