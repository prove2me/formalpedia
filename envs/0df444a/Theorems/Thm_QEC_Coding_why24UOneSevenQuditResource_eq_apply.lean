-- Prove2me | Theorems.Thm_QEC_Coding_why24UOneSevenQuditResource_eq_apply
-- name    : QEC.Coding.why24UOneSevenQuditResource_eq_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:08:51.282765+00:00
-- url     : https://prove2.me/theorems/4c293884-88d4-47d9-b53a-c77933ec6e73
-- title:
--   Coding: why24 UOne Seven Qudit Resource eq apply
-- statement:
--   The qudit resource is literally the source diagonal applied to its plus input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L95-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L95-L97

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24UOneSevenQuditResource_eq_apply :
    why24UOneSevenQuditResource = why24UOneSeven why24QuditPlusState := by sorry
