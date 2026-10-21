-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_arbitrary_index_attainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.arbitrary_index_attainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:59:39.073805+00:00
-- url     : https://prove2.me/theorems/23875c91-906e-4940-b32d-8348b0fbb0a3
-- title:
--   Remark 3.7: arbitrary index sets
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   For every index set $I$, with no countability or nonemptiness assumption, and every Banach space $Y$,
--
--   $$
--   \mathrm{NA}_{\mathcal N}(c_0(I),Y)=\mathcal N(c_0(I),Y),\qquad \mathrm{NA}_\pi(\ell_1(I)\widehat\otimes_\pi Y)=\ell_1(I)\widehat\otimes_\pi Y.
--   $$
--
--   Each attaining representation remains a countable series, even for an uncountable index set.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 9, Remark 3.7: arbitrary index sets

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

section SequenceResults

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

/-- PDF p.9, Remark 3.7: arbitrary index sets, including empty and uncountable ones;
individual representing series are still countable. -/
theorem arbitrary_index_attainment (I : Type*) :
    (∀ T : Nuclear K (CZero K I) Y, NuclearAttains T) ∧
    (∀ z : Projective K (LOne K I) Y, TensorAttains z) := by sorry

end SequenceResults

end QAlgorithms.Papers.Independent.Renew46.P04

end
