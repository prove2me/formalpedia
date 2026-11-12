-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionTrace_eight_visitsTarget_action
-- name    : QEC.Distillation.PhaseInjection.phaseInjectionTrace_eight_visitsTarget_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:41:24.459081+00:00
-- url     : https://prove2.me/theorems/6a4e5753-abb5-4592-b23d-9a7bfa4e2743
-- title:
--   Phase Injection: phase Injection Trace eight visits Target action
-- statement:
--   An order-eight target visit exposes a concrete `-π / 4` trace prefix with its target action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1184-L1193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1184-L1193

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

theorem QEC.Distillation.PhaseInjection.phaseInjectionTrace_eight_visitsTarget_action
    (coins : List Bool) (target : ZMod 8) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.visitsTarget (0 : ZMod 8) target coins) :
    ∃ initial suffix, coins = initial ++ suffix ∧
      (repeatedPhaseInjectionTrace (phaseCycleAngle 8) initial psi hpsi).1 =
        phaseInjectionHistoryGlobalPhase (phaseCycleAngle 8) initial •
          phaseEightTargetAction target psi := by sorry
