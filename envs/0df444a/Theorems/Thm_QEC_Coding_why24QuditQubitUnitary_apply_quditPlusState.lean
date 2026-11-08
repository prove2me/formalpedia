-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_apply_quditPlusState
-- name    : QEC.Coding.why24QuditQubitUnitary_apply_quditPlusState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:09:00.658426+00:00
-- url     : https://prove2.me/theorems/622018c5-9a78-48cc-b3bc-bd3b6957af42
-- title:
--   Coding: why24 Qudit Qubit Unitary apply qudit Plus State
-- statement:
--   The selected basis unitary sends the source qudit plus state to its qubit image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L80-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean#L80-L82

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding

theorem QEC.Coding.why24QuditQubitUnitary_apply_quditPlusState :
    why24QuditQubitUnitary why24QuditPlusState = why24QubitPlusState := by sorry
