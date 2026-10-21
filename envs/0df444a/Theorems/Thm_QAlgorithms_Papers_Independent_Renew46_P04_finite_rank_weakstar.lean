-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_finite_rank_weakstar
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.finite_rank_weakstar
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:15:15.536127+00:00
-- url     : https://prove2.me/theorems/62ad3b8e-27b2-4b3b-aa41-8ec476e03196
-- title:
--   Lemma 5.2: finite-rank unit-ball weak-star closure
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Assume $Y^*$ is separable. Let $j_Y:Y\to Y^{**}$ be the canonical bidual inclusion. In the weak-star topology with predual $P(X,Y^*)$,
--
--   $$
--   B_{\mathcal F(X,Y^{**})}\subseteq\overline{\{j_Y\circ A:A\in\mathcal F(X,Y),\ \|A\|\le1\}}^{\,w^*}.
--   $$
--
--   Both balls are closed operator-norm unit balls. The source predual, rather than the weak operator topology, is used by testing all completed tensors.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 20, Lemma 5.2: finite-rank unit-ball weak-star closure

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- PDF p.20, Lemma 5.2: the finite-rank closed unit ball in X to Y** lies in the
weak-star closure of the finite-rank closed unit ball in X to Y, canonically embedded. -/
theorem finite_rank_weakstar [CompleteSpace X] [CompleteSpace Y] [TopologicalSpace.SeparableSpace (Y →L[K] K)]
    (T : X →L[K] ((Y →L[K] K) →L[K] K))
    (hfin : FiniteDimensional K T.toLinearMap.range) (hn : ‖T‖ ≤ 1) :
    InTensorWeakStarClosure
      {S | ∃ A : X →L[K] Y, FiniteDimensional K A.range ∧ ‖A‖ ≤ 1 ∧
        S = (NormedSpace.inclusionInDoubleDual K Y).comp A} T := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
