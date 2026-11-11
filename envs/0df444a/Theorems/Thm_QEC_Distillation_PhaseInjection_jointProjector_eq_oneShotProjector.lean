-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_jointProjector_eq_oneShotProjector
-- name    : QEC.Distillation.PhaseInjection.jointProjector_eq_oneShotProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:20:31.658302+00:00
-- url     : https://prove2.me/theorems/a2a27f99-f3a9-4c0f-8a5d-2742ebe9c4da
-- title:
--   Phase Injection: joint Projector eq one Shot Projector
-- statement:
--   A one-check joint projector reduces to its selected literal spectral projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L85-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L85-L90

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

theorem QEC.Distillation.PhaseInjection.jointProjector_eq_oneShotProjector (outcome : StabilizerOutcome) :
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
        (fun _ => outcome) = oneShotProjector outcome := by sorry
