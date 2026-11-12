-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionTrace_target_of_endpoint
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_target_of_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:19:56.305099+00:00
-- url     : https://prove2.me/theorems/030a4ec6-b980-49cc-a253-ee75c58ef224
-- title:
--   Phase Injection: repeated Phase Injection Trace target of endpoint
-- statement:
--   The output component of a resource-carrying trace realizes a residue hit as a target action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1089-L1096
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1089-L1096

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjectionTrace_target_of_endpoint {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod q) coins = target) :
    (repeatedPhaseInjectionTrace (phaseCycleAngle q) coins psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle q) coins •
        phaseCycleTargetAction q target psi := by sorry
