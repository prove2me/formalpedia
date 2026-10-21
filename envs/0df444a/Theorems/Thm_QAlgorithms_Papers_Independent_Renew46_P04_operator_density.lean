-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_operator_density
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.operator_density
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:04:34.742968+00:00
-- url     : https://prove2.me/theorems/12096183-29a8-428d-b849-349072e535a4
-- title:
--   Corollary 3.11: operator density into the dual
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Assume $X$ is nonzero. If every tensor in $P(X,Y)$ attains its projective norm, then
--
--   $$
--   \overline{\mathrm{NA}(X,Y^*)}^{\|\cdot\|}=\mathcal L(X,Y^*).
--   $$
--
--   Only the domain must be nonzero; $Y=0$ is permitted. The codomain is the dual $Y^*$, and ordinary operator attainment is used.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 10, Corollary 3.11: operator density into the dual

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

/-- PDF p.10, Corollary 3.11: operator density into Y*.
The printed statement does not exclude X=0. We require nonzero X because its
unit sphere would otherwise be empty; Y=0 remains allowed. -/
theorem operator_density [CompleteSpace X] [CompleteSpace Y] [Nontrivial X] (h : ∀ z : Projective K X Y, TensorAttains z) :
    Dense {T : X →L[K] (Y →L[K] K) | OperatorAttains T} := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
