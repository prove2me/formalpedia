-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_finite_dimensional_tensors
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.finite_dimensional_tensors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:57:50.119355+00:00
-- url     : https://prove2.me/theorems/64d240ec-007a-4017-a59d-6fc03231bae4
-- title:
--   Proposition 3.5: finite-dimensional factors
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If both $X$ and $Y$ are finite dimensional, then
--
--   $$
--   \mathrm{NA}_\pi(P(X,Y))=P(X,Y).
--   $$
--
--   Every tensor, including zero and tensors with a zero-dimensional factor, has an attaining bounded representation.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 8, Proposition 3.5: finite-dimensional factors

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

/-- PDF p.8, Proposition 3.5: finite-dimensional factors, including zero factors and zero tensors. -/
theorem finite_dimensional_tensors [FiniteDimensional K X] [FiniteDimensional K Y] :
    ∀ z : Projective K X Y, TensorAttains z := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
