-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjection_target_of_endpoint
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjection_target_of_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:19:47.705766+00:00
-- url     : https://prove2.me/theorems/ecf00f5a-2a29-46bb-ad0f-4aed29791f2a
-- title:
--   Phase Injection: repeated Phase Injection target of endpoint
-- statement:
--   A concrete retry endpoint realizes the corresponding target phase action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1079-L1086
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1079-L1086

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjection_target_of_endpoint {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod q) coins = target) :
    repeatedPhaseInjection (phaseCycleAngle q) coins psi hpsi =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle q) coins •
        phaseCycleTargetAction q target psi := by sorry
