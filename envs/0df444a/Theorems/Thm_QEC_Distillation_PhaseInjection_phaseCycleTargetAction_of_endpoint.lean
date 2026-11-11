-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseCycleTargetAction_of_endpoint
-- name    : QEC.Distillation.PhaseInjection.phaseCycleTargetAction_of_endpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:22:51.854394+00:00
-- url     : https://prove2.me/theorems/3a976deb-c11f-44e5-82ca-711e6a63f5b9
-- title:
--   Phase Injection: phase Cycle Target Action of endpoint
-- statement:
--   A residue hit gives the target phase action, with the `2π` ambiguity discharged in the operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1047-L1076
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1047-L1076

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct

theorem QEC.Distillation.PhaseInjection.phaseCycleTargetAction_of_endpoint {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod q) coins = target) :
    OneQubitMagic.phaseShiftOperator (phaseInjectionHistoryAngle (phaseCycleAngle q) coins) =
      phaseCycleTargetAction q target := by sorry
