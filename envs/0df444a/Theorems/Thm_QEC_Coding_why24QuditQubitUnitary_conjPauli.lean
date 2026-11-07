-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conjPauli
-- name    : QEC.Coding.why24QuditQubitUnitary_conjPauli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:55.348372+00:00
-- url     : https://prove2.me/theorems/88fe7bc3-72c7-4964-acb6-db5b8241bf06
-- title:
--   Coding: why24 Qudit Qubit Unitary conj Pauli
-- statement:
--   The selected-coordinate unitary sends every source-labelled Pauli to its binary label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L295-L308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L295-L308

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitUnitary_conjPauli (P : Why24FieldPauli) :
    why24QuditQubitUnitary.conjOperator (why24FieldPauliOperator P) =
      why24BinaryPauliOperator (why24PauliLabelEquiv P) := by sorry
