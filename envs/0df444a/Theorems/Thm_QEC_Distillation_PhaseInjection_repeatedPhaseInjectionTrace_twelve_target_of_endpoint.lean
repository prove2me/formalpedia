-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionTrace_twelve_target_of_endpoint
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_twelve_target_of_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:41:19.44081+00:00
-- url     : https://prove2.me/theorems/cc4be987-b3fe-4799-a7cd-49a2ac50f3ff
-- title:
--   Phase Injection: repeated Phase Injection Trace twelve target of endpoint
-- statement:
--   An order-twelve endpoint hit realizes its `-π / 6` target action in the concrete trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1174-L1181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1174-L1181

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_twelve_target_of_endpoint
    (coins : List Bool) (target : ZMod 12) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod 12) coins = target) :
    (repeatedPhaseInjectionTrace (phaseCycleAngle 12) coins psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle 12) coins •
        phaseTwelveTargetAction target psi := by sorry
