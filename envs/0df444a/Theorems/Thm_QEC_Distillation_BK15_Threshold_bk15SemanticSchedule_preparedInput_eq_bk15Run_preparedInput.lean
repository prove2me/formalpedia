-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_preparedInput_eq_bk15Run_preparedInput
-- name    : QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_preparedInput_eq_bk15Run_preparedInput
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:27:46.12623+00:00
-- url     : https://prove2.me/theorems/65463361-c23d-4df5-a383-50a54dfaab0f
-- title:
--   Threshold: bk15 Semantic Schedule prepared Input eq bk15 Run prepared Input
-- statement:
--   The prepared tensor state of a semantic node is exactly the prepared
--   input used by its matching actual BK15 run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L992-L1015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L992-L1015

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

theorem QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_preparedInput_eq_bk15Run_preparedInput
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    BK15SemanticSchedule.preparedInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
        ((bk15Run
          (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
          (bk15Iteration_pos_and_lt_epsilonStar
            (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) := by sorry
