-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_attainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.bilinear_attainment
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:02:43.415411+00:00
-- url     : https://prove2.me/theorems/2fb44091-3b62-43af-9588-12fd97a3e149
-- title:
--   Lemma 3.9: bilinear attainment from an attaining tensor
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Let $B:X\times Y\to\mathbb K$ be a bounded bilinear form. Suppose it attains its functional norm on the projective product at an attaining unit tensor $z$. Then
--
--   $$
--   \|z\|_\pi=1,\quad z\in\mathrm{NA}_\pi,\quad |\widetilde B(z)|=\|B\|\quad\Longrightarrow\quad B\in\mathrm{NA}(X\times Y).
--   $$
--
--   Bilinear attainment means attainment at a pair of unit vectors, not just as an operator into a dual.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 9, Lemma 3.9: bilinear attainment from an attaining tensor

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

/-- PDF pp.9–10, Lemma 3.9: the functional attains at a unit attaining tensor. -/
theorem bilinear_attainment [CompleteSpace X] [CompleteSpace Y] (B : Bilinear K X Y K) (z : Projective K X Y)
    (hz : ‖z‖ = 1) (ha : TensorAttains z) (hB : ‖extendBilinear B z‖ = ‖B‖) :
    BilinearAttains B := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
