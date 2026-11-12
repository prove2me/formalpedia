-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PhaseInjection_correctedErroredTInvAttempt_action
-- name    : QEC.Distillation.HH18PhaseInjection.correctedErroredTInvAttempt_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:41:27.977123+00:00
-- url     : https://prove2.me/theorems/3072093c-131e-4bda-9404-0c93aab37ba3
-- title:
--   HH18 Phase Injection: corrected Errored TInv Attempt action
-- statement:
--   Both corrected errored branches implement a physical data `Z` after the
--   same ideal `T†` action, retaining only the existing branch scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L235-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PhaseInjection.lean#L235-L259

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PhaseInjection
open Semantics Semantics.Qubit

theorem QEC.Distillation.HH18PhaseInjection.correctedErroredTInvAttempt_action (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    correctedErroredTInvAttempt psi hpsi coin =
      PhaseInjection.oneShotAttemptGlobalPhase tInvErrorAngle coin •
        pauliZ (OneQubitMagic.phaseShiftOperator tInvIdealAngle psi) := by sorry
