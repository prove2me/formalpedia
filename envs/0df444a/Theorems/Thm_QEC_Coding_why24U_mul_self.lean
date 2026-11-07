-- Prove2me | Theorems.Thm_QEC_Coding_why24U_mul_self
-- name    : QEC.Coding.why24U_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:20:10.668755+00:00
-- url     : https://prove2.me/theorems/0e45f3c2-dae8-47ad-a80c-93ffd0848cfb
-- title:
--   Coding: why24 U mul self
-- statement:
--   Applying a source diagonal twice is the identity operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L69-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L69-L74

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24U_mul_self (β : F1024) (n : ℕ) :
    why24U β n * why24U β n = 1 := by sorry
