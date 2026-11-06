-- Prove2me | Theorems.Thm_QEC_Locality_wordPauliTwirlFactorized_eq_refill_comp_erasure
-- name    : QEC.Locality.wordPauliTwirlFactorized_eq_refill_comp_erasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:39.699269+00:00
-- url     : https://prove2.me/theorems/0880bd5c-01dd-46bd-a4dd-07431a7de9ff
-- title:
--   Locality: word Pauli Twirl Factorized eq refill comp erasure
-- statement:
--   The Locality construction uses the word Pauli Twirl Factorized eq refill comp erasure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L954-L964
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L954-L964

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.wordPauliTwirlFactorized_eq_refill_comp_erasure (S : FiniteSubsystem ι) :
    wordPauliTwirlFactorized S =
      QuantumChannel.comp (refillFactorized S) S.erasureChannel := by sorry
