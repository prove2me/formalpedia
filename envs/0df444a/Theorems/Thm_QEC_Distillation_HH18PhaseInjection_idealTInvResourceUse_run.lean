-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_idealTInvResourceUse_run
-- name    : QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:31:34.560488+00:00
-- url     : https://prove2.me/theorems/e33091d2-cf33-4c92-9c62-081082510513
-- title:
--   HH18 Phase Injection: ideal TInv Resource Use run
-- statement:
--   Running the ideal resource use produces the literal phase-injection input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L106-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L106-L111

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_run (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (PhaseInjection.phaseStateResourceUse tInvIdealAngle).run
        (PhaseInjection.sourceInputDensity psi hpsi) =
      PhaseInjection.injectionInputDensity psi tInvIdealAngle hpsi := by sorry
