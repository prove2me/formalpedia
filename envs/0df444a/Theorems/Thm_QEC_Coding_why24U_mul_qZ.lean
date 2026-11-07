-- Prove2me | Theorems.Thm_QEC_Coding_why24U_mul_qZ
-- name    : QEC.Coding.why24U_mul_qZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:19:55.081075+00:00
-- url     : https://prove2.me/theorems/24c94aad-6a18-4615-a5eb-0fdf6041b65c
-- title:
--   Coding: why24 U mul q Z
-- statement:
--   Every source diagonal commutes with every concrete trace-phase `Z` operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L322-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/U7Gate.lean#L322-L326

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24U_mul_qZ (β : F1024) (n : ℕ) (γ : F1024) :
    why24U β n * why24QuditZ γ = why24QuditZ γ * why24U β n := by sorry
