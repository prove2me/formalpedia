-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_root_resourceCount
-- name    : QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_root_resourceCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:27:37.40466+00:00
-- url     : https://prove2.me/theorems/ed40159b-d649-44e0-a582-7f8fdcedbf9e
-- title:
--   Threshold: bk15 Semantic Schedule root resource Count
-- statement:
--   The matching concrete BK15 run consumes exactly the fifteen derived
--   resources stored at every semantic internal node.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L980-L988
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L980-L988

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

theorem QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_root_resourceCount
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    (bk15Run
      (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
      (bk15Iteration_pos_and_lt_epsilonStar
        (bk15HInputError rho) hpositive hthreshold depth).1).resourceCount = 15 := by sorry
