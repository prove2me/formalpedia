-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_extension
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.bilinear_extension
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:49:12.446347+00:00
-- url     : https://prove2.me/theorems/1ee7ab08-0d74-4dd2-a37f-8fe6f7bcc6fc
-- title:
--   §2.2: canonical bilinear extension isometry
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   For every Banach space $Z$, the computed restriction and extension maps give a linear isometric equivalence between bounded bilinear maps $B:X\times Y\to Z$ and bounded linear maps $P(X,Y)\to Z$. The extension is the unique continuous linear map satisfying
--
--   $$
--   \widetilde B(x\otimes y)=B(x,y),\qquad \widetilde B\!\left(\sum_nx_n\otimes y_n\right)=\sum_nB(x_n,y_n).
--   $$
--
--   The series equality is a convergent-sum assertion for every admissible representation. This is the canonical completed universal property; the Lean bilinear type uses precisely two multilinear coordinates.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 3, §2.2: canonical bilinear extension isometry

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

/-- PDF pp.3–4, §2.2: actual canonical extension/restriction maps form an isometry;
continuous extensions are unique, and absolutely summable series are evaluated termwise. -/
theorem bilinear_extension [CompleteSpace X] [CompleteSpace Y] :
    (∃ E : Bilinear K X Y Z ≃ₗᵢ[K] (Projective K X Y →L[K] Z),
      (∀ B, E B = extendBilinear B) ∧ (∀ L, E.symm L = restrictBilinear L)) ∧
    (∀ (B : Bilinear K X Y Z) x y, extendBilinear B (pure x y) = B (pair x y)) ∧
    (∀ (B : Bilinear K X Y Z) (L : Projective K X Y →L[K] Z),
      (∀ x y, L (pure x y) = B (pair x y)) → L = extendBilinear B) ∧
    (∀ (B : Bilinear K X Y Z) z x y, TensorRep z x y →
      HasSum (fun n => B (pair (x n) (y n))) (extendBilinear B z)) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
