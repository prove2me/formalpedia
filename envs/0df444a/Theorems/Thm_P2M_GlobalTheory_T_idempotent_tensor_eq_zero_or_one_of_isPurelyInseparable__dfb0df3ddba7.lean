-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable__dfb0df3ddba7
-- name    : P2M_GlobalTheory_T_idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable__dfb0df3ddba7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:22.551794+00:00
-- url     : https://prove2.me/theorems/801d634e-5e30-4662-bed6-d55e271f9ed5
-- title:
--   P2 M Global Theory T idempotent tensor eq zero or one of is Purely Inseparable  dfb0df3ddba7: P2 M Global Theory T idempotent tensor eq zero or one of is Purely Inseparable  dfb0df3ddba7
-- statement:
--   The P2 M Global Theory T idempotent tensor eq zero or one of is Purely Inseparable  dfb0df3ddba7 construction uses the P2 M Global Theory T idempotent tensor eq zero or one of is Purely Inseparable  dfb0df3ddba7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentTensorEqZeroOrOneOfIsPurelyInseparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable__dfb0df3ddba7 : ∀ (k K B : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B] (e : K ⊗[k] B), IsIdempotentElem e → e = 0 ∨ e = 1 := by sorry

alias «GlobalTheory».«T».«idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable'» := P2M_GlobalTheory_T_idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable__dfb0df3ddba7
