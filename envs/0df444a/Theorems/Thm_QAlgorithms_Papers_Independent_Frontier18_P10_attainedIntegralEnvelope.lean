-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_attainedIntegralEnvelope
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.attainedIntegralEnvelope
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:07:23.150035+00:00
-- url     : https://prove2.me/theorems/57782775-fea2-4adf-a8cf-6673afd3152b
-- title:
--   Proposition 6: attained integral representation of convex closure
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   Assume $A$ is convex and $\mu$-compact, and $f:A\to(-\infty,+\infty]$ is lower semicontinuous and bounded below by a finite real constant. For every $x\in A$,
--   $$\overline{\operatorname{co}}f(x)=\inf_{\mu\in M(A):\,b(\mu)=x}\int_A f\,d\mu,$$
--   and some measure in this fiber attains the infimum. The integral is the extended Lebesgue integral formed from positive and negative parts. Moreover,
--   $$f(x)=\overline{\operatorname{co}}f(x)\quad(x\in\operatorname{extr}A).$$
--
--
--   This is the attained integral representation, including the source’s p.10 extreme-point consequence.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 8, Proposition 6: attained integral representation of convex closure

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

/-- Proposition 6, PDF p.8, and its explicitly stated extreme-point
consequence on PDF p.10. Costs may equal positive infinity; the integral uses
positive and negative parts, and attainment is a conclusion. -/
theorem attainedIntegralEnvelope (A : Set E) (hA : GeneralBarycenterSpace A)
    (hc : Convex ℝ A) (hm : MuCompact A) (f : E → EReal)
    (hlsc : LowerSemicontinuous (fun x : A => f x))
    (hlower : ∃ c : ℝ, ∀ x ∈ A, (c : EReal) ≤ f x) :
    (∀ x ∈ A,
      closedConvexHullFunction A f x =
        ⨅ (mu : ProbabilityMeasure A) (_ : pettisBarycenter A mu = x),
          extendedIntegral (mu : Measure A) (fun y : A => f y)) ∧
    (∀ x ∈ A, ∃ mu : ProbabilityMeasure A,
      pettisBarycenter A mu = x ∧
      closedConvexHullFunction A f x =
        extendedIntegral (mu : Measure A) (fun y : A => f y)) ∧
    (∀ x ∈ A.extremePoints ℝ, f x = closedConvexHullFunction A f x) := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
