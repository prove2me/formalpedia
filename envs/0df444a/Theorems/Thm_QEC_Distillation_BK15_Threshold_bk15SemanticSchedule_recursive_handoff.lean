-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_recursive_handoff
-- name    : QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_recursive_handoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:30:52.767557+00:00
-- url     : https://prove2.me/theorems/d6c4e126-e258-4f81-8e8e-38ff11617d7a
-- title:
--   Threshold: bk15 Semantic Schedule recursive handoff
-- statement:
--   A parent semantic node obtains each resource by dephasing the selected
--   root output of the corresponding complete child schedule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1033-L1043
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1033-L1043

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

theorem QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_recursive_handoff
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar)
    (depth : Nat) (site : Fin 15) :
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 2)) site =
      aBasisDephasing.mapDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1))) := by sorry
