-- Prove2me | Theorems.Thm_QEC_Locality_erasureRecoverableFromRegister_of_localPauliTwirl_correctable
-- name    : QEC.Locality.erasureRecoverableFromRegister_of_localPauliTwirl_correctable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:37:54.262891+00:00
-- url     : https://prove2.me/theorems/224d2f2a-3c43-49e5-9bd4-75ac653545cf
-- title:
--   Locality: erasure Recoverable From Register of local Pauli Twirl correctable
-- statement:
--   The Locality construction uses the erasure Recoverable From Register of local Pauli Twirl correctable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L1037-L1055
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L1037-L1055

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

theorem QEC.Locality.erasureRecoverableFromRegister_of_localPauliTwirl_correctable
    (S : FiniteSubsystem ι) (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel (Qubit.QubitRegister ι) (Qubit.QubitRegister ι))
    (h : Correctable (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) C
      (localPauliTwirl S) recovery) :
    S.ErasureRecoverableFromRegister C := by sorry
