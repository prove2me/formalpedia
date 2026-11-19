-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_eventually_lt
-- name    : QEC.Distillation.BK15.Threshold.bk15Iteration_eventually_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:26:49.514922+00:00
-- url     : https://prove2.me/theorems/78969180-96e5-434d-a25d-8d3c0929d482
-- title:
--   Threshold: bk15 Iteration eventually lt
-- statement:
--   Every positive target error is reached after finitely many accepted rounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L617-L622
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L617-L622

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

theorem QEC.Distillation.BK15.Threshold.bk15Iteration_eventually_lt
    (epsilon target : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (htarget : 0 < target) :
    ∃ rounds : Nat, bk15Iteration epsilon rounds < target := by sorry
