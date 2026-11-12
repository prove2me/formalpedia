-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionTrace_eight_target_of_endpoint
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_eight_target_of_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:41:14.828148+00:00
-- url     : https://prove2.me/theorems/dc4dccc0-4905-48e5-a9a1-6ce54dc7b43c
-- title:
--   Phase Injection: repeated Phase Injection Trace eight target of endpoint
-- statement:
--   An order-eight endpoint hit realizes its `-π / 4` target action in the concrete trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1164-L1171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1164-L1171

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_eight_target_of_endpoint
    (coins : List Bool) (target : ZMod 8) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod 8) coins = target) :
    (repeatedPhaseInjectionTrace (phaseCycleAngle 8) coins psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle 8) coins •
        phaseEightTargetAction target psi := by sorry
