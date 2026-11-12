-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_erroredTInvResourceUse_resource
-- name    : QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_resource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:32:42.926037+00:00
-- url     : https://prove2.me/theorems/0e206dda-ecbc-4d7b-9fa8-c80930a70179
-- title:
--   HH18 Phase Injection: errored TInv Resource Use resource
-- statement:
--   The errored injection use consumes the exact selected HH18 error density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L98-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L98-L103

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_resource :
    (PhaseInjection.phaseStateResourceUse tInvErrorAngle).resource =
      HH18NoisyInput.tInvResourceErrorDensity 1 := by sorry
