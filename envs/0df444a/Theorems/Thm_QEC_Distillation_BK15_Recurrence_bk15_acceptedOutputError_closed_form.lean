-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15_acceptedOutputError_closed_form
-- name    : QEC.Distillation.BK15.Recurrence.bk15_acceptedOutputError_closed_form
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:16:44.664851+00:00
-- url     : https://prove2.me/theorems/5ca22652-8274-4fb6-bae7-3905bfff7cd6
-- title:
--   Recurrence: bk15 accepted Output Error closed form
-- statement:
--   The actual decoded accepted output of the packaged BK15 run has the
--   Bravyi--Kitaev negative-A error recurrence on the strict source interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2520-L2532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L2520-L2532

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

theorem QEC.Distillation.BK15.Recurrence.bk15_acceptedOutputError_closed_form
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    bk15OutputError (bk15Run epsilon hpositive).acceptedOutput aZeroDensity =
      (1 - 15 * bk15_r epsilon ^ 7 + 15 * bk15_r epsilon ^ 8 -
        bk15_r epsilon ^ 15) / (2 * (1 + 15 * bk15_r epsilon ^ 8)) := by sorry
