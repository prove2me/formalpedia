-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_idealTInvResourceUse_resource
-- name    : QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_resource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:32:09.7282+00:00
-- url     : https://prove2.me/theorems/cc526c43-5fe3-4c59-bf3a-b25dc05d889e
-- title:
--   HH18 Phase Injection: ideal TInv Resource Use resource
-- statement:
--   The ideal injection use consumes the exact zero-error HH18 resource density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L89-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L89-L95

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_resource :
    (PhaseInjection.phaseStateResourceUse tInvIdealAngle).resource =
      HH18NoisyInput.tInvResourceErrorDensity 0 := by sorry
