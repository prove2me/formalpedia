-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_choquetChains
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.choquetChains
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:06:12.116206+00:00
-- url     : https://prove2.me/theorems/fa69e9ec-8a74-47fa-b0a8-7fa1658751ba
-- title:
--   Lemma 1: Choquet chains
-- statement:
--   Let $A$ be a closed, von Neumann bounded subset of a Hausdorff locally convex real linear space. Assume its closed convex hull, with the induced topology and additive uniformity, is complete, separable and metrizable. Write $M(A)$ for Borel probability measures with weak convergence against bounded continuous functions, and $b(\mu)$ for the Pettis barycenter. Write $\operatorname{co}f$ and $\overline{\operatorname{co}}f$ for the greatest convex minorant and the greatest lower semicontinuous convex minorant, respectively.
--
--   Assume $A$ is convex and pointwise $\mu$-compact: each set of measures with a fixed barycenter is compact. For $\mu,\nu\in M(A)$ write $\mu\preceq\nu$ when $\int f\,d\mu\le\int f\,d\nu$ for every bounded continuous convex real $f$. Every nonempty chain $C\subseteq M(A)$ has a least upper bound:
--   $$\exists\eta\in M(A):\quad (\forall\mu\in C,\ \mu\preceq\eta)\quad\text{and}\quad
--   \forall\nu\in M(A),\ (\forall\mu\in C,\mu\preceq\nu)\Rightarrow\eta\preceq\nu.$$
--
--
--   The nonempty-chain convention is the one used by the source proof.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 7, Lemma 1: Choquet chains

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

/-- Lemma 1, PDF p.7: every nonempty Choquet chain has a least upper bound.
Nonemptiness follows the proof's convention that a chain is a net in one fiber;
the empty-chain reading is false on a nontrivial segment. -/
theorem choquetChains (A : Set E) (hA : GeneralBarycenterSpace A)
    (hc : Convex ℝ A) (hm : PointwiseMuCompact A)
    (C : Set (ProbabilityMeasure A)) (hne : C.Nonempty)
    (hchain : ∀ mu ∈ C, ∀ nu ∈ C, ChoquetLE A mu nu ∨ ChoquetLE A nu mu) :
    ∃ upper : ProbabilityMeasure A,
      (∀ mu ∈ C, ChoquetLE A mu upper) ∧
      ∀ other : ProbabilityMeasure A,
        (∀ mu ∈ C, ChoquetLE A mu other) → ChoquetLE A upper other := by sorry

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
