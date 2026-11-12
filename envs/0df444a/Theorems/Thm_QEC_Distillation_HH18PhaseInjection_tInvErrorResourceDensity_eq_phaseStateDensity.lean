-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvErrorResourceDensity_eq_phaseStateDensity
-- name    : QEC.Distillation.HH18PhaseInjection.tInvErrorResourceDensity_eq_phaseStateDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:33:54.670279+00:00
-- url     : https://prove2.me/theorems/c4a69de7-2eee-40b7-96a0-f63222f192ce
-- title:
--   HH18 Phase Injection: t Inv Error Resource Density eq phase State Density
-- statement:
--   The selected nonzero HH18 error density is the canonical shifted phase density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L77-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L77-L86

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.tInvErrorResourceDensity_eq_phaseStateDensity :
    HH18NoisyInput.tInvResourceErrorDensity 1 =
      OneQubitMagic.phaseStateDensity tInvErrorAngle := by sorry
