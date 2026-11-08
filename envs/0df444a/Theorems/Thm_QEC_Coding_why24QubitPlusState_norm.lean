-- Prove2me | Theorems.Thm_QEC_Coding_why24QubitPlusState_norm
-- name    : QEC.Coding.why24QubitPlusState_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:09:44.84135+00:00
-- url     : https://prove2.me/theorems/1db852af-e809-40df-aa56-477d8276b314
-- title:
--   Coding: why24 Qubit Plus State norm
-- statement:
--   The transported ten-qubit plus state has unit norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L85-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L85-L88

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24QubitPlusState_norm : ‖why24QubitPlusState‖ = 1 := by sorry
