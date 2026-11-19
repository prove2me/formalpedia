-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_realizesRun
-- name    : QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_realizesRun
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:28:27.859496+00:00
-- url     : https://prove2.me/theorems/8063a0dc-0acf-458f-ab68-096af47804d3
-- title:
--   Threshold: bk15 Semantic Schedule realizes Run
-- statement:
--   The concrete run realization exposed by a semantic internal node.  This
--   is a proved interface, not a property stored in the schedule data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1047-L1082
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1047-L1082

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

theorem QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_realizesRun
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    (bk15Run
      (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
      (bk15Iteration_pos_and_lt_epsilonStar
        (bk15HInputError rho) hpositive hthreshold depth).1).resourceCount = 15 ∧
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
    BK15SemanticSchedule.preparedInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
        ((bk15Run
          (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
          (bk15Iteration_pos_and_lt_epsilonStar
            (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
    BK15SemanticSchedule.rootOutput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput := by sorry
