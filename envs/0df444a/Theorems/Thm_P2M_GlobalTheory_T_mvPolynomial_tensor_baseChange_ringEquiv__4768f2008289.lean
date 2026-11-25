-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_mvPolynomial_tensor_baseChange_ringEquiv__4768f2008289
-- name    : P2M_GlobalTheory_T_mvPolynomial_tensor_baseChange_ringEquiv__4768f2008289
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:32.397843+00:00
-- url     : https://prove2.me/theorems/c74ae77c-6e13-58df-b243-87bdefb406fb
-- title:
--   P2 M Global Theory T mv Polynomial tensor base Change ring Equiv  4768f2008289: P2 M Global Theory T mv Polynomial tensor base Change ring Equiv  4768f2008289
-- statement:
--   The P2 M Global Theory T mv Polynomial tensor base Change ring Equiv  4768f2008289 construction uses the P2 M Global Theory T mv Polynomial tensor base Change ring Equiv  4768f2008289 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialTensorBaseChangeRingEquivStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialTensorBaseChangeRingEquivStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialTensorBaseChangeRingEquiv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialTensorBaseChangeRingEquivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_mvPolynomial_tensor_baseChange_ringEquiv__4768f2008289 : ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K] [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K], letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) := (MvPolynomial.map (algebraMap S B)).toAlgebra; Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by sorry

alias «GlobalTheory».«T».«mvPolynomial_tensor_baseChange_ringEquiv'» := P2M_GlobalTheory_T_mvPolynomial_tensor_baseChange_ringEquiv__4768f2008289
