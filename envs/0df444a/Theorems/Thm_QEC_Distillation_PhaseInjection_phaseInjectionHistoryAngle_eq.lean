-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionHistoryAngle_eq
-- name    : QEC.Distillation.PhaseInjection.phaseInjectionHistoryAngle_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:23:05.071432+00:00
-- url     : https://prove2.me/theorems/b01cf0c3-d569-4425-ac29-79aef759b477
-- title:
--   Phase Injection: phase Injection History Angle eq
-- statement:
--   The concrete signed angle is the phase-cycle unit times the integer retry exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1010-L1018
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L1010-L1018

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

theorem QEC.Distillation.PhaseInjection.phaseInjectionHistoryAngle_eq (theta : Real) (coins : List Bool) :
    phaseInjectionHistoryAngle theta coins =
      theta * (phaseInjectionHistoryExponent coins : Real) := by sorry
