-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditPlusState_norm
-- name    : QEC.Coding.why24QuditPlusState_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:09:07.928714+00:00
-- url     : https://prove2.me/theorems/a21d1aa8-176c-4aa9-8fdc-35e4419adeab
-- title:
--   Coding: why24 Qudit Plus State norm
-- statement:
--   The concrete uniform qudit input has unit norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L66-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L66-L73

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24QuditPlusState_norm : ‖why24QuditPlusState‖ = 1 := by sorry
