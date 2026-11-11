-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjection_action
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjection_action
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:22:10.729739+00:00
-- url     : https://prove2.me/theorems/595b1fd5-00c7-4e56-949e-a54f8b105fdd
-- title:
--   Phase Injection: repeated Phase Injection action
-- statement:
--   A repeated concrete circuit implements the signed history angle, up to its explicit global phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L976-L990
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L976-L990

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjection_action (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    repeatedPhaseInjection theta coins psi hpsi =
      phaseInjectionHistoryGlobalPhase theta coins •
        OneQubitMagic.phaseShiftOperator (phaseInjectionHistoryAngle theta coins) psi := by sorry
