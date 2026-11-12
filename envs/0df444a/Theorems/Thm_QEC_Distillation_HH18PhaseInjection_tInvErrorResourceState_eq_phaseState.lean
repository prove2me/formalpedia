-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvErrorResourceState_eq_phaseState
-- name    : QEC.Distillation.HH18PhaseInjection.tInvErrorResourceState_eq_phaseState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:53:28.711601+00:00
-- url     : https://prove2.me/theorems/49e819e6-ed51-431e-bacf-02bb4a33b838
-- title:
--   HH18 Phase Injection: t Inv Error Resource State eq phase State
-- statement:
--   The selected nonzero HH18 error branch is the canonical shifted phase state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L69-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L69-L74

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.tInvErrorResourceState_eq_phaseState :
    HH18NoisyInput.tInvResourceErrorState 1 =
      OneQubitMagic.phaseState tInvErrorAngle := by sorry
