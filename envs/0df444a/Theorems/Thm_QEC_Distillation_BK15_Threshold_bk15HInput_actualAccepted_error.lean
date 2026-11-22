-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInput_actualAccepted_error
-- name    : QEC.Distillation.BK15.Threshold.bk15HInput_actualAccepted_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:28:37.137542+00:00
-- url     : https://prove2.me/theorems/09478deb-64ea-44b4-a7d0-124ddff598c5
-- title:
--   Threshold: bk15 HInput actual Accepted error
-- statement:
--   On the strict H branch, the first selected accepted execution is the
--   actual #707 BK15 run and has the certified recurrence error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1086-L1097
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1086-L1097

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

theorem QEC.Distillation.BK15.Threshold.bk15HInput_actualAccepted_error
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    bk15Recurrence (bk15HInputError rho) =
      bk15OutputError
        (bk15Run (bk15HInputEpsilon rho hpositive hleHalf)
          (bk15HInputEpsilon_pos rho hpositive hleHalf)).acceptedOutput
        aZeroDensity := by sorry
