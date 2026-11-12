-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionTrace_twelve_visitsTarget_action
-- name    : QEC.Distillation.PhaseInjection.phaseInjectionTrace_twelve_visitsTarget_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:42:25.580428+00:00
-- url     : https://prove2.me/theorems/fea15a92-1d9b-4b9a-aa19-40f32bcf3866
-- title:
--   Phase Injection: phase Injection Trace twelve visits Target action
-- statement:
--   An order-twelve target visit exposes a concrete `-π / 6` trace prefix with its target action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1196-L1205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1196-L1205

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

theorem QEC.Distillation.PhaseInjection.phaseInjectionTrace_twelve_visitsTarget_action
    (coins : List Bool) (target : ZMod 12) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.visitsTarget (0 : ZMod 12) target coins) :
    ∃ initial suffix, coins = initial ++ suffix ∧
      (repeatedPhaseInjectionTrace (phaseCycleAngle 12) initial psi hpsi).1 =
        phaseInjectionHistoryGlobalPhase (phaseCycleAngle 12) initial •
          phaseTwelveTargetAction target psi := by sorry
