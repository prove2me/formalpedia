-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_normalizesPaulis_iff
-- name    : QEC.Coding.why24QuditQubitUnitary_normalizesPaulis_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:02.735548+00:00
-- url     : https://prove2.me/theorems/4654d5e0-4e97-4067-bd7f-c01332b4b2ac
-- title:
--   Coding: why24 Qudit Qubit Unitary normalizes Paulis iff
-- statement:
--   The concrete field-Pauli normalizer transports to the concrete binary-Pauli normalizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L369-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L369-L413

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitUnitary_normalizesPaulis_iff (C : Semantics.Operator Why24QuditSpace) :
    why24BinaryNormalizesPaulis (why24QuditQubitUnitary.conjOperator C) ↔
      why24FieldNormalizesPaulis C := by sorry
