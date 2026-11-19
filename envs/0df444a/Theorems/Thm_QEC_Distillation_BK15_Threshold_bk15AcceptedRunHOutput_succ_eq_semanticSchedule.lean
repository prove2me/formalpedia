-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15AcceptedRunHOutput_succ_eq_semanticSchedule
-- name    : QEC.Distillation.BK15.Threshold.bk15AcceptedRunHOutput_succ_eq_semanticSchedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:28:51.830426+00:00
-- url     : https://prove2.me/theorems/7a55df74-85a9-45a7-9d46-6b12c145a8ac
-- title:
--   Threshold: bk15 Accepted Run HOutput succ eq semantic Schedule
-- statement:
--   The strict returned H output is the inverse transport of the semantic
--   schedule's actual root accepted density, rather than a detached scalar layer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1246-L1256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L1246-L1256

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

theorem QEC.Distillation.BK15.Threshold.bk15AcceptedRunHOutput_succ_eq_semanticSchedule
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (rounds : Nat) :
    bk15AcceptedRunHOutput rho (rounds + 1) =
      sourceA0Transport.symm.conjDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hpositive hthreshold (rounds + 1))) := by sorry
