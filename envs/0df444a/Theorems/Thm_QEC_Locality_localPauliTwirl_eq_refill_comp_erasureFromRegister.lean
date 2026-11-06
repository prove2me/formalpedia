-- Prove2me | Theorems.Thm_QEC_Locality_localPauliTwirl_eq_refill_comp_erasureFromRegister
-- name    : QEC.Locality.localPauliTwirl_eq_refill_comp_erasureFromRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:53.890098+00:00
-- url     : https://prove2.me/theorems/c039733d-5116-4552-977d-8ff0b287c1e8
-- title:
--   Locality: local Pauli Twirl eq refill comp erasure From Register
-- statement:
--   The Locality construction uses the local Pauli Twirl eq refill comp erasure From Register property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L1025-L1035
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L1025-L1035

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

theorem QEC.Locality.localPauliTwirl_eq_refill_comp_erasureFromRegister (S : FiniteSubsystem ι) :
    localPauliTwirl S =
      QuantumChannel.comp (localPauliRefill S) S.erasureChannelFromRegister := by sorry
