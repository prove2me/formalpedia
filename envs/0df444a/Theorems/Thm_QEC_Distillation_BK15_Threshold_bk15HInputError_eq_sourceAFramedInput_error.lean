-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInputError_eq_sourceAFramedInput_error
-- name    : QEC.Distillation.BK15.Threshold.bk15HInputError_eq_sourceAFramedInput_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:30:08.519474+00:00
-- url     : https://prove2.me/theorems/5008b6d6-e3f1-4453-b340-f08ed4e2b9b3
-- title:
--   Threshold: bk15 HInput Error eq source AFramed Input error
-- statement:
--   The literal H-to-source-A transport identifies the analytic entry error
--   with the actual framed input's negative-A error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L796-L800
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L796-L800

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

theorem QEC.Distillation.BK15.Threshold.bk15HInputError_eq_sourceAFramedInput_error
    (rho : DensityOperator QubitSpace) :
    bk15HInputError rho = aInputError (sourceAFramedInput rho) := by sorry
