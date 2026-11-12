-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_correctedTInvBasisAmplitude_eq
-- name    : QEC.Distillation.HH18Parameterized.correctedTInvBasisAmplitude_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:56:30.433069+00:00
-- url     : https://prove2.me/theorems/27958098-aac2-4073-ae9d-d4792b2ea817
-- title:
--   HH18 Parameterized: corrected TInv Basis Amplitude eq
-- statement:
--   Each local diagonal entry is its measured scalar, resource-error sign,
--   and ideal `T†` phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L76-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L76-L95

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

theorem QEC.Distillation.HH18Parameterized.correctedTInvBasisAmplitude_eq
    (error : ZMod 2) (coin : Bool) (bit : Fin 2) :
    correctedTInvBasisAmplitude error coin bit =
      PhaseInjection.oneShotAttemptGlobalPhase
          (tInvResourceAngle error) coin *
        (if error = 0 then 1 else zPhase bit) *
          OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle * bit.val) := by sorry
