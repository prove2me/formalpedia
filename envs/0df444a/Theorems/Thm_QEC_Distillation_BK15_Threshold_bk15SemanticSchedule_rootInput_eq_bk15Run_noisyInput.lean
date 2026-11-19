-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput
-- name    : QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:25:11.520935+00:00
-- url     : https://prove2.me/theorems/5eb5518c-6e63-4b02-861f-7fbdbc3b342b
-- title:
--   Threshold: bk15 Semantic Schedule root Input eq bk15 Run noisy Input
-- statement:
--   Each semantic internal node supplies the same fifteen resources as its
--   actual BK15 run at the matching recurrence depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L959-L976
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L959-L976

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

theorem QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput := by sorry
