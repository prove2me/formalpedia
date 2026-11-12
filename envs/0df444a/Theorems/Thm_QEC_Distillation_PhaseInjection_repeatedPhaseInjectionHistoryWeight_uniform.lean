-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_repeatedPhaseInjectionHistoryWeight_uniform
-- name    : QEC.Distillation.PhaseInjection.repeatedPhaseInjectionHistoryWeight_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:21:43.92968+00:00
-- url     : https://prove2.me/theorems/82e2d991-6bc6-4bb6-99ad-6fc7cc75eb6c
-- title:
--   Phase Injection: repeated Phase Injection History Weight uniform
-- statement:
--   The concrete fresh-resource measurement trace is uniformly fair.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L921-L932
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L921-L932

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

theorem QEC.Distillation.PhaseInjection.repeatedPhaseInjectionHistoryWeight_uniform (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    repeatedPhaseInjectionHistoryWeight theta coins psi hpsi =
      (1 / 2 : Real) ^ coins.length := by sorry
