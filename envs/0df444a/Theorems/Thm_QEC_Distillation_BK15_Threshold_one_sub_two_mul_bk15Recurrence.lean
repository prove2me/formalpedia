-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_one_sub_two_mul_bk15Recurrence
-- name    : QEC.Distillation.BK15.Threshold.one_sub_two_mul_bk15Recurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:25:19.814577+00:00
-- url     : https://prove2.me/theorems/7d5a4147-86ae-4157-b546-c70a7ce3e3ad
-- title:
--   Threshold: one sub two mul bk15 Recurrence
-- statement:
--   The transformed recurrence used for fixed-point and sign analysis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L64-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L64-L72

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

theorem QEC.Distillation.BK15.Threshold.one_sub_two_mul_bk15Recurrence (epsilon : Real) :
    1 - 2 * bk15Recurrence epsilon =
      bk15Bias epsilon ^ 7 * (15 + bk15Bias epsilon ^ 8) /
        (1 + 15 * bk15Bias epsilon ^ 8) := by sorry
