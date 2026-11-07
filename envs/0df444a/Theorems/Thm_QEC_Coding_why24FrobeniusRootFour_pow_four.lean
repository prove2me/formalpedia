-- Prove2me | Theorems.Thm_QEC_Coding_why24FrobeniusRootFour_pow_four
-- name    : QEC.Coding.why24FrobeniusRootFour_pow_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:20:08.608725+00:00
-- url     : https://prove2.me/theorems/21b53e20-76a1-416b-9b13-11562b08b3fe
-- title:
--   Coding: why24 Frobenius Root Four pow four
-- statement:
--   The chosen fourth-root representative has fourth power equal to its input in `F1024`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L119-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L119-L124

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24FrobeniusRootFour_pow_four (x : F1024) :
    why24FrobeniusRootFour x ^ 4 = x := by sorry
