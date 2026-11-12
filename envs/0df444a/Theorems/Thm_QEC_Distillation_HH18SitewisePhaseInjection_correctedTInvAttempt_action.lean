-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_correctedTInvAttempt_action
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.correctedTInvAttempt_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:53:20.464194+00:00
-- url     : https://prove2.me/theorems/82afcce0-a8d4-4724-8b9b-526efca5e4b3
-- title:
--   HH18 Sitewise Phase Injection: corrected TInv Attempt action
-- statement:
--   Binary error selection specializes the accepted ideal/error covariance theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L51-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L51-L70

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SitewisePhaseInjection
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators

theorem QEC.Distillation.HH18SitewisePhaseInjection.correctedTInvAttempt_action (error : ZMod 2) (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    correctedTInvAttempt error psi hpsi coin =
      PhaseInjection.oneShotAttemptGlobalPhase
          (tInvResourceAngle error) coin •
        (if error = 0 then
          OneQubitMagic.phaseShiftOperator
            HH18PhaseInjection.tInvIdealAngle psi
        else
          pauliZ (OneQubitMagic.phaseShiftOperator
            HH18PhaseInjection.tInvIdealAngle psi)) := by sorry
