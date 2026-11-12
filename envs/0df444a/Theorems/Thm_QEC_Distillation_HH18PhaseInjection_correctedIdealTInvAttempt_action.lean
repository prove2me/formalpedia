-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_correctedIdealTInvAttempt_action
-- name    : QEC.Distillation.HH18PhaseInjection.correctedIdealTInvAttempt_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:41:20.864361+00:00
-- url     : https://prove2.me/theorems/f5066eac-33b6-417e-af4d-63eafb680358
-- title:
--   HH18 Phase Injection: corrected Ideal TInv Attempt action
-- statement:
--   Both corrected ideal branches implement physical `T†`, retaining only the
--   existing explicit source-vector global scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L213-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L213-L231

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.correctedIdealTInvAttempt_action (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    correctedIdealTInvAttempt psi hpsi coin =
      PhaseInjection.oneShotAttemptGlobalPhase tInvIdealAngle coin •
        OneQubitMagic.phaseShiftOperator tInvIdealAngle psi := by sorry
