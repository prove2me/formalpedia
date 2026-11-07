-- Prove2me | Theorems.Thm_QEC_Coding_why24_trace_sq
-- name    : QEC.Coding.why24_trace_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:18:56.163147+00:00
-- url     : https://prove2.me/theorems/d5e8b9e9-3687-4169-b0f1-509941c44a64
-- title:
--   Coding: why24 trace sq
-- statement:
--   The absolute trace is invariant under a Frobenius square on the concrete field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L127-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L127-L136

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24_trace_sq (x : F1024) :
    Algebra.trace (ZMod 2) F1024 (x ^ 2) = Algebra.trace (ZMod 2) F1024 x := by sorry
