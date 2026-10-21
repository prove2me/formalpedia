-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_nuclear_dual
-- name    : QAlgorithms.Papers.Independent.Renew46.P04.nuclear_dual
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:53:20.370985+00:00
-- url     : https://prove2.me/theorems/2e060fa1-06d2-4262-b9c4-f197986f07d0
-- title:
--   §2.2: nuclear dual and kernel annihilator
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $X,Y$ be Banach spaces over $\mathbb K$. Write $P(X,Y)=X\widehat\otimes_\pi Y$, with its projective norm. A tensor attains this norm when it has a bounded countable pure-tensor representation, convergent with summable norm products, whose cost equals its norm. Write $\mathcal N(X,Y)$ for the range of the canonical map $J:P(X^*,Y)\to\mathcal L(X,Y)$, equipped with the quotient nuclear norm, and $\mathrm{NA}_{\mathcal N}$ for operators having an attaining series in this norm. All duals are continuous linear duals.
--
--   Pullback by the actual quotient map identifies the nuclear dual isometrically with the annihilator $(\ker J)^\perp$ in $P(X^*,Y)^*$. If $H\in\mathcal N(X,Y)^*$ and $G$ is its pullback, then every admissible representation of $T$ satisfies
--
--   $$
--   H(T)=\sum_nG(f_n\otimes y_n).
--   $$
--
--   The series is asserted to converge to $H(T)$. Equivalently $G$ is evaluated as a bilinear map on $(f_n,y_n)$; no tensor lift attaining the quotient norm is assumed.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, PDF p. 4, §2.2: nuclear dual and kernel annihilator

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

/-- PDF p.4: duality of the quotient and its kernel annihilator, with the series pairing. -/
theorem nuclear_dual :
    ∃ E : (Nuclear K X Y →L[K] K) ≃ₗᵢ[K] Annihilator (K := K) (X := X) (Y := Y),
      (∀ H, (E H).val = pullNuclearDual H) ∧
      ∀ (T : Nuclear K X Y) f y, NuclearRep (nuclearOperator T) f y →
        ∀ H : Nuclear K X Y →L[K] K,
          HasSum (fun n => (E H).val (pure (f n) (y n))) (H T) := by sorry

end Banach

end QAlgorithms.Papers.Independent.Renew46.P04

end
