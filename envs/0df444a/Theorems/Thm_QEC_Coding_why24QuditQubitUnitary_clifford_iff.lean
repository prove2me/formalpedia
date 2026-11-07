-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_clifford_iff
-- name    : QEC.Coding.why24QuditQubitUnitary_clifford_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:51.311127+00:00
-- url     : https://prove2.me/theorems/59c9240d-436e-4bc5-8aef-fb3da593b083
-- title:
--   Coding: why24 Qudit Qubit Unitary clifford iff
-- statement:
--   The selected-coordinate transport preserves the source-local Clifford normalizer exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L416-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L416-L420

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitUnitary_clifford_iff (C : Semantics.Operator Why24QuditSpace) :
    Why24BinaryClifford (why24QuditQubitUnitary.conjOperator C) ↔ Why24FieldClifford C := by sorry
