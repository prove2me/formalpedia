-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_density
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.bilinear_density
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:03:08.096897+00:00
-- url     : https://prove2.me/theorems/f73fbe2f-aff1-48d0-8def-70e972148687
-- title:
--   Proposition 3.10: tensor attainment implies bilinear density
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Assume $X$ and $Y$ are nonzero. Universal tensor norm attainment implies density of classical norm-attaining bilinear forms:
--
--   $$
--   \mathrm{NA}_\pi(P(X,Y))=P(X,Y)\quad\Longrightarrow\quad \overline{\mathrm{NA}(X\times Y)}^{\|\cdot\|}=\mathcal B(X\times Y).
--   $$
--
--   The nonzero-space convention is necessary because a zero factor has empty unit sphere. Mere tensor density is not the hypothesis.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 10, Proposition 3.10: tensor attainment implies bilinear density

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

/-- PDF p.10, Proposition 3.10: universal tensor attainment implies norm density.
The printed statement does not exclude zero factors. We require both factors
nonzero: otherwise the classical attaining set is empty and cannot be dense. -/
theorem bilinear_density [CompleteSpace X] [CompleteSpace Y] [Nontrivial X] [Nontrivial Y]
    (h : ∀ z : Projective K X Y, TensorAttains z) :
    Dense {B : Bilinear K X Y K | BilinearAttains B} := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
