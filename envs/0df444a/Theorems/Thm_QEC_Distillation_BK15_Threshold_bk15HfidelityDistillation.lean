-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HfidelityDistillation
-- name    : QEC.Distillation.BK15.Threshold.bk15HfidelityDistillation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:31:27.072875+00:00
-- url     : https://prove2.me/theorems/83f23556-07c4-40f8-b660-b121a8f53c40
-- title:
--   Threshold: bk15 Hfidelity Distillation
-- statement:
--   Any input above `FStar` has either the separately proved raw ideal endpoint
--   or a finite semantic selected-accepted BK15 schedule.  In the strict branch,
--   the witness exposes the exact `15^k` leaf count, derived resource input,
--   prepared tensor input, actual accepted root, and returned H density; it makes
--   no retry-cost, yield, or probability claim.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1362-L1412
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1362-L1412

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.bk15HfidelityDistillation
    (rho : DensityOperator QubitSpace)
    (hfidelity : FStar < hFidelity rho) (delta : Real) (hdelta : 0 < delta) :
    ∃ rounds : Nat,
      bk15AcceptedRunHInfidelity rho rounds < delta ∧
        (bk15HInputError rho = 0 ∨
          ∃ (hpositive : 0 < bk15HInputError rho)
            (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat),
            rounds = depth + 1 ∧
            BK15SemanticSchedule.leafCount
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              15 ^ (depth + 1) ∧
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
                  (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput ∧
            bk15AcceptedRunHOutput rho (depth + 1) =
              sourceA0Transport.symm.conjDensity
                (BK15SemanticSchedule.rootOutput
                  (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)))) := by sorry
