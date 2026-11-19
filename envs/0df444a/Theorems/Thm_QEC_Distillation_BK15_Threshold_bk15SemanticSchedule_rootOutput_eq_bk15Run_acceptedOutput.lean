-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
-- name    : QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:25:13.726215+00:00
-- url     : https://prove2.me/theorems/4aaebe2b-4c96-4bfa-899d-b482d59d18c1
-- title:
--   Threshold: bk15 Semantic Schedule root Output eq bk15 Run accepted Output
-- statement:
--   The root density stored by a complete semantic internal node is the actual
--   normalized accepted output of its matching BK15 run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1019-L1029
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1019-L1029

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

theorem QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    BK15SemanticSchedule.rootOutput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput := by sorry
