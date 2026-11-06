-- Prove2me | Theorems.Thm_QEC_Locality_localPauliTwirl_eq_transport
-- name    : QEC.Locality.localPauliTwirl_eq_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:40:57.820678+00:00
-- url     : https://prove2.me/theorems/bad312b7-ed34-4080-9b74-57080ffbd9c9
-- title:
--   Locality: local Pauli Twirl eq transport
-- statement:
--   The Locality construction uses the local Pauli Twirl eq transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L999-L1006
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L999-L1006

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

theorem QEC.Locality.localPauliTwirl_eq_transport (S : FiniteSubsystem ι) :
    localPauliTwirl S =
      QuantumChannel.comp (QuantumChannel.unitaryConj S.registerFactorization.symm)
        (QuantumChannel.comp (wordPauliTwirlFactorized S)
          (QuantumChannel.unitaryConj S.registerFactorization)) := by sorry
