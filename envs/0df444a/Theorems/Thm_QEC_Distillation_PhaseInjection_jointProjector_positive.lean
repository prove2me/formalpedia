-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_jointProjector_positive
-- name    : QEC.Distillation.PhaseInjection.jointProjector_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:22:19.31802+00:00
-- url     : https://prove2.me/theorems/74f1d3fa-54fe-4e6c-96d2-2d8f8a088818
-- title:
--   Phase Injection: joint Projector positive
-- statement:
--   The actual positive joint-syndrome projector is the existing even projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L93-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L93-L100

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

theorem QEC.Distillation.PhaseInjection.jointProjector_positive :
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute positiveSyndrome =
      TwoQubit.zzEvenProjector := by sorry
