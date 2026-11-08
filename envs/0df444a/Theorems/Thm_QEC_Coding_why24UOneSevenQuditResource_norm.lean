-- Prove2me | Theorems.Thm_QEC_Coding_why24UOneSevenQuditResource_norm
-- name    : QEC.Coding.why24UOneSevenQuditResource_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:08:36.824995+00:00
-- url     : https://prove2.me/theorems/d44415bc-8868-487f-8685-18b8dfc66ccd
-- title:
--   Coding: why24 UOne Seven Qudit Resource norm
-- statement:
--   The source qudit resource has unit norm by the concrete diagonal's unitarity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L100-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L100-L111

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24UOneSevenQuditResource_norm : ‖why24UOneSevenQuditResource‖ = 1 := by sorry
