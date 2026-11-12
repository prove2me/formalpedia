-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_correctedTInvAttempt_action
-- name    : QEC.Distillation.HH18Parameterized.correctedTInvAttempt_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:56:29.52476+00:00
-- url     : https://prove2.me/theorems/f55dfdb7-9225-4655-99fd-a0e753bfa769
-- title:
--   HH18 Parameterized: corrected TInv Attempt action
-- statement:
--   Binary error selection specializes the established ideal/error covariance
--   of the one-qubit corrected injection circuit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L45-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L45-L64

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.correctedTInvAttempt_action (error : ZMod 2) (psi : QubitSpace)
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
