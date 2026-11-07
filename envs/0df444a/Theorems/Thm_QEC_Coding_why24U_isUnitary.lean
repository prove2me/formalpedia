-- Prove2me | Theorems.Thm_QEC_Coding_why24U_isUnitary
-- name    : QEC.Coding.why24U_isUnitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:19:42.274025+00:00
-- url     : https://prove2.me/theorems/e21380d6-31ad-4006-b8b4-0786f3bdb299
-- title:
--   Coding: why24 U is Unitary
-- statement:
--   The source diagonal preserves the concrete qudit inner product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L77-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L77-L87

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24U_isUnitary (β : F1024) (n : ℕ) :
    Why24IsUnitary (why24U β n) := by sorry
