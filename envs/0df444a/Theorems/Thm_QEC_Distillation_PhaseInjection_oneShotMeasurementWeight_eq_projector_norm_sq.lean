-- Prove2me | Theorems.Thm_QEC_Distillation_PhaseInjection_oneShotMeasurementWeight_eq_projector_norm_sq
-- name    : QEC.Distillation.PhaseInjection.oneShotMeasurementWeight_eq_projector_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:21:34.392728+00:00
-- url     : https://prove2.me/theorems/03d95f50-73ac-4cbb-ac50-76acf0add19a
-- title:
--   Phase Injection: one Shot Measurement Weight eq projector norm sq
-- statement:
--   The instrument Born weight is the squared norm of its literal projector branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L817-L827
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean#L817-L827

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

theorem QEC.Distillation.PhaseInjection.oneShotMeasurementWeight_eq_projector_norm_sq
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) (coin : Bool) :
    oneShotMeasurementWeight psi theta hpsi coin =
      oneShotProjectedWeight psi theta coin := by sorry
