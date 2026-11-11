-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionTrace_visitsTarget_action
-- name    : QEC.Distillation.PhaseInjection.phaseInjectionTrace_visitsTarget_action
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:20:04.916545+00:00
-- url     : https://prove2.me/theorems/01ac353e-29d4-4512-9865-eb1e1abeea42
-- title:
--   Phase Injection: phase Injection Trace visits Target action
-- statement:
--   An actual cyclic target visit exposes a concrete resource-trace prefix with that target action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1124-L1133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1124-L1133

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

theorem QEC.Distillation.PhaseInjection.phaseInjectionTrace_visitsTarget_action {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.visitsTarget (0 : ZMod q) target coins) :
    ∃ initial suffix, coins = initial ++ suffix ∧
      (repeatedPhaseInjectionTrace (phaseCycleAngle q) initial psi hpsi).1 =
        phaseInjectionHistoryGlobalPhase (phaseCycleAngle q) initial •
          phaseCycleTargetAction q target psi := by sorry
