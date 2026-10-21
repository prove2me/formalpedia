-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_c0_l1_attainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.c0_l1_attainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:58:21.503791+00:00
-- url     : https://prove2.me/theorems/85d2de26-72ae-49dd-9a8b-6563c1852f34
-- title:
--   Proposition 3.6(a,b): c0 operators and ℓ1 tensors
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   For every Banach space $Y$, both conclusions hold:
--
--   $$
--   \mathrm{NA}_{\mathcal N}(c_0,Y)=\mathcal N(c_0,Y),\qquad \mathrm{NA}_\pi(\ell_1\widehat\otimes_\pi Y)=\ell_1\widehat\otimes_\pi Y.
--   $$
--
--   These are the two equivalent universal-attainment formulations in Proposition 3.6; both clauses, across the page break, are included.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 8, Proposition 3.6(a,b): c0 operators and ℓ1 tensors

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

/-- PDF pp.8–9, Proposition 3.6(a,b): both c0 nuclear operators and l1 tensors attain. -/
theorem c0_l1_attainment :
    (∀ T : Nuclear K (CZero K ℕ) Y, NuclearAttains T) ∧
    (∀ z : Projective K (LOne K ℕ) Y, TensorAttains z) := by sorry

end SequenceResults

end QAlgorithms.Papers.Independent.Renew46.P04

end
