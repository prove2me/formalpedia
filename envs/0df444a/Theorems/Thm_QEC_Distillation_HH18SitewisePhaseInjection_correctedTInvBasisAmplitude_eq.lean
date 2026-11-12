-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_correctedTInvBasisAmplitude_eq
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.correctedTInvBasisAmplitude_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:54:52.759099+00:00
-- url     : https://prove2.me/theorems/c79d1b87-7356-44e8-aaca-dd24806b7ff3
-- title:
--   HH18 Sitewise Phase Injection: corrected TInv Basis Amplitude eq
-- statement:
--   Each local diagonal entry is its measured scalar, resource-error sign, and ideal `T†` phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L81-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L81-L100

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

theorem QEC.Distillation.HH18SitewisePhaseInjection.correctedTInvBasisAmplitude_eq
    (error : ZMod 2) (coin : Bool) (bit : Fin 2) :
    correctedTInvBasisAmplitude error coin bit =
      PhaseInjection.oneShotAttemptGlobalPhase
          (tInvResourceAngle error) coin *
        (if error = 0 then 1 else zPhase bit) *
          OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle * bit.val) := by sorry
