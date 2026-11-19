-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_eq_actual_acceptedOutputError
-- name    : QEC.Distillation.BK15.Threshold.bk15Recurrence_eq_actual_acceptedOutputError
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:24:58.152762+00:00
-- url     : https://prove2.me/theorems/8553fe2a-79a7-4d36-a9af-2df0427f5888
-- title:
--   Threshold: bk15 Recurrence eq actual accepted Output Error
-- statement:
--   The scalar coordinate is exactly the error of #707's actual accepted
--   BK15 run on every strict physical input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L56-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L56-L61

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.bk15Recurrence_eq_actual_acceptedOutputError
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    bk15Recurrence epsilon.epsilon =
      bk15OutputError (bk15Run epsilon hpositive).acceptedOutput aZeroDensity := by sorry
