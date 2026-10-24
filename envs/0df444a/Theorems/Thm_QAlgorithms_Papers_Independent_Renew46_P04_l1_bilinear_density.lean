-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_l1_bilinear_density
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.l1_bilinear_density
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:17:33.211207+00:00
-- url     : https://prove2.me/theorems/4c29b798-e4c1-40b5-9b56-6c36e7e78dba
-- title:
--   Unnumbered §6: ℓ1 bilinear density
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   For every nonzero Banach space $Y$,
--
--   $$
--   \overline{\mathrm{NA}(\ell_1\times Y)}^{\|\cdot\|}=\mathcal B(\ell_1\times Y).
--   $$
--
--   This is the explicit unnumbered consequence in §6. The source’s implicit nonzero-range convention is required by its two-unit-sphere notion of bilinear attainment.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 23, Unnumbered §6: ℓ1 bilinear density

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

/-- PDF p.23, unnumbered consequence: l1 bilinear norm density.
The printed consequence does not exclude Y=0. We require nonzero Y because
sphere-based bilinear attainment is otherwise empty and cannot be dense. -/
theorem l1_bilinear_density [CompleteSpace Y] [Nontrivial Y] :
    Dense {B : Bilinear K (LOne K ℕ) Y K | BilinearAttains B} := by sorry

end SequenceResults

end QAlgorithms.Papers.Independent.Renew46.P04

end
