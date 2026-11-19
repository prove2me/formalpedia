-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_tendsto_zero
-- name    : QEC.Distillation.BK15.Threshold.bk15Iteration_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:26:43.746826+00:00
-- url     : https://prove2.me/theorems/5225ff76-d898-40bb-8882-2ba1a21da1e2
-- title:
--   Threshold: bk15 Iteration tendsto zero
-- statement:
--   Below the exact threshold, recursive accepted BK15 errors converge to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L562-L614
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L562-L614

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

theorem QEC.Distillation.BK15.Threshold.bk15Iteration_tendsto_zero
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) :
    Filter.Tendsto (bk15Iteration epsilon) Filter.atTop (nhds 0) := by sorry
