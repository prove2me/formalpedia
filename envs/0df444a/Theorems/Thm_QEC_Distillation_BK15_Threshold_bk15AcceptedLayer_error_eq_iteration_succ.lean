-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15AcceptedLayer_error_eq_iteration_succ
-- name    : QEC.Distillation.BK15.Threshold.bk15AcceptedLayer_error_eq_iteration_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:24:40.338685+00:00
-- url     : https://prove2.me/theorems/59a46c18-fa36-41f1-8c40-7e7408cc4f5f
-- title:
--   Threshold: bk15 Accepted Layer error eq iteration succ
-- statement:
--   Each scheduled layer is #707's actual normalized accepted BK15 output,
--   and its source-A error is the next genuine iterate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L652-L663
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L652-L663

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

theorem QEC.Distillation.BK15.Threshold.bk15AcceptedLayer_error_eq_iteration_succ
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    bk15OutputError (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
      aZeroDensity = bk15Iteration epsilon (rounds + 1) := by sorry
