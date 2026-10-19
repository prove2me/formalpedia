-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_extremeEnvelopeCharacterization
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.extremeEnvelopeCharacterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:10:36.230157+00:00
-- url     : https://prove2.me/theorems/555e29ae-fef1-44d3-8b8e-0f5d6c226c96
-- title:
--   Proposition 8: extreme points via convex envelopes
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   For convex $\mu$-compact $A$,
--   $$\operatorname{extr}A=\{x\in A:\ f(x)=\overline{\operatorname{co}}f(x)
--   \text{ for every bounded continuous concave real }f\}.$$
--
--
--   The restricted concave test class characterizes the extreme boundary.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 10, Proposition 8: extreme points via convex envelopes

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

/-- Proposition 8, PDF p.10: equality with the closed convex envelope for
all bounded continuous concave tests characterizes the extreme points. -/
theorem extremeEnvelopeCharacterization (A : Set E)
    (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A) (hm : MuCompact A) :
    A.extremePoints ℝ = {x ∈ A | ∀ f : E → ℝ,
      BoundedContinuousOn A f → ConcaveOn ℝ A f →
      (f x : EReal) = closedConvexHullFunction A (fun y => (f y : EReal)) x} := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
