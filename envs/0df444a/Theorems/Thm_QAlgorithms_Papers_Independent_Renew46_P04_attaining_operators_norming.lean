-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_attaining_operators_norming
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.attaining_operators_norming
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:16:19.072221+00:00
-- url     : https://prove2.me/theorems/ae202e88-b9b9-4cb0-adcc-c440cbda379c
-- title:
--   Remark 5.4: a norming operator family
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   If attaining tensors are dense in $P(X,Y)$, then the classically norm-attaining operators into $Y^*$ in the closed unit ball form a norming family. In unit-sphere form this means
--
--   $$
--   \forall z\in S_{P(X,Y)}\ \forall\varepsilon>0\ \exists T\in\mathrm{NA}(X,Y^*),\quad\|T\|\le1,\quad|\widetilde T(z)|>1-\varepsilon.
--   $$
--
--   This formulation is vacuous when the tensor space is zero and avoids using an empty real supremum as a substantive norm identity.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 22, Remark 5.4: a norming operator family

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

/-- PDF p.22, Remark 5.4: norming classical operators in the closed operator unit ball. -/
theorem attaining_operators_norming (h : TensorDense K X Y) :
    TensorNorming {T : X →L[K] (Y →L[K] K) | OperatorAttains T ∧ ‖T‖ ≤ 1} := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
