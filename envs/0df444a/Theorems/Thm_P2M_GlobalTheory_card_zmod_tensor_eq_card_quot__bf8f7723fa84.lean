-- Prove2me | Theorems.Thm_P2M_GlobalTheory_card_zmod_tensor_eq_card_quot__bf8f7723fa84
-- name    : P2M_GlobalTheory_card_zmod_tensor_eq_card_quot__bf8f7723fa84
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:52.044791+00:00
-- url     : https://prove2.me/theorems/397e2874-d2bb-4a69-a423-cf7f4e777339
-- title:
--   P2 M Global Theory card zmod tensor eq card quot  bf8f7723fa84: P2 M Global Theory card zmod tensor eq card quot  bf8f7723fa84
-- statement:
--   The P2 M Global Theory card zmod tensor eq card quot  bf8f7723fa84 construction uses the P2 M Global Theory card zmod tensor eq card quot  bf8f7723fa84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiples.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiples.lean#L25-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem P2M_GlobalTheory_card_zmod_tensor_eq_card_quot__bf8f7723fa84 : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ),
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by sorry

alias «GlobalTheory».«card_zmod_tensor_eq_card_quot'» := P2M_GlobalTheory_card_zmod_tensor_eq_card_quot__bf8f7723fa84
