-- Prove2me | Theorems.Thm_QEC_Coding_why24QuditZ_mul
-- name    : QEC.Coding.why24QuditZ_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:19:41.378774+00:00
-- url     : https://prove2.me/theorems/ed058fe3-522b-41b6-a5fe-fbec574586cd
-- title:
--   Coding: why24 Qudit Z mul
-- statement:
--   Concrete trace phases multiply according to addition of their field labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L313-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L313-L319

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24QuditZ_mul (γ δ : F1024) :
    why24QuditZ γ * why24QuditZ δ = why24QuditZ (γ + δ) := by sorry
