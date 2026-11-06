-- Prove2me | Theorems.Thm_QEC_Locality_localPauliFamily_operator_supportedOnRegister
-- name    : QEC.Locality.localPauliFamily_operator_supportedOnRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:49:08.818598+00:00
-- url     : https://prove2.me/theorems/ce7ce0fe-f077-4cab-b27a-e5acce92a7df
-- title:
--   Locality: local Pauli Family operator supported On Register
-- statement:
--   The Locality construction uses the local Pauli Family operator supported On Register property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L987-L992
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L987-L992

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

theorem QEC.Locality.localPauliFamily_operator_supportedOnRegister (S : FiniteSubsystem ι)
    (p : LocalPauliWordIndex S) :
    S.OperatorSupportedOnRegister ((localPauliFamily S).operator p) := by sorry
