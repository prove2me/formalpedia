-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15_recurrence_scaled_denominator_pos
-- name    : QEC.Distillation.BK15.Recurrence.bk15_recurrence_scaled_denominator_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:16:48.131282+00:00
-- url     : https://prove2.me/theorems/74fd8415-9e02-450e-af29-2985685276b8
-- title:
--   Recurrence: bk15 recurrence scaled denominator pos
-- statement:
--   Positivity of the exact denominator used by the accepted output error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L46-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L46-L48

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct

theorem QEC.Distillation.BK15.Recurrence.bk15_recurrence_scaled_denominator_pos (epsilon : BK15Epsilon) :
    0 < 2 * (1 + 15 * bk15_r epsilon ^ 8) := by sorry
