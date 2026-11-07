-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_conjUOneSeven
-- name    : QEC.Coding.why24QuditQubitUnitary_conjUOneSeven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:35:09.786191+00:00
-- url     : https://prove2.me/theorems/7b54d0ed-439b-46e9-872e-7d3f2a1779e6
-- title:
--   Coding: why24 Qudit Qubit Unitary conj UOne Seven
-- statement:
--   The transported qubit operator is definitionally the concrete conjugate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L1424-L1425
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L1424-L1425

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditQubitUnitary_conjUOneSeven :
    why24QuditQubitUnitary.conjOperator why24UOneSeven = why24QubitUOneSeven := by sorry
