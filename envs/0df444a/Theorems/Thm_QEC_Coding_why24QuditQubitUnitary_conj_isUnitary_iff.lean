-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conj_isUnitary_iff
-- name    : QEC.Coding.why24QuditQubitUnitary_conj_isUnitary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:47.379386+00:00
-- url     : https://prove2.me/theorems/260e1cb1-d4e9-4376-a02d-98a89b0d482a
-- title:
--   Coding: why24 Qudit Qubit Unitary conj is Unitary iff
-- statement:
--   Conjugation by the selected unitary preserves unitarity in both directions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L352-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L352-L358

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitUnitary_conj_isUnitary_iff (C : Semantics.Operator Why24QuditSpace) :
    Why24IsUnitary (why24QuditQubitUnitary.conjOperator C) ↔ Why24IsUnitary C := by sorry
