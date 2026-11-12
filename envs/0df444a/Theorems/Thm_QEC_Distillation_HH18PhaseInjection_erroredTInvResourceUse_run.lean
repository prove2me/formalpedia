-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_erroredTInvResourceUse_run
-- name    : QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:31:28.690228+00:00
-- url     : https://prove2.me/theorems/6573fac6-1390-4533-a7b7-8566585b11b8
-- title:
--   HH18 Phase Injection: errored TInv Resource Use run
-- statement:
--   Running the errored resource use produces the literal shifted-angle input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L114-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L114-L119

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_run (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (PhaseInjection.phaseStateResourceUse tInvErrorAngle).run
        (PhaseInjection.sourceInputDensity psi hpsi) =
      PhaseInjection.injectionInputDensity psi tInvErrorAngle hpsi := by sorry
