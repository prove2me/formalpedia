-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_physicalTInv_apply
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.physicalTInv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:53:51.686212+00:00
-- url     : https://prove2.me/theorems/a28da3d1-8576-49d8-94de-d8e10f110b71
-- title:
--   HH18 Sitewise Phase Injection: physical TInv apply
-- statement:
--   The inverse physical HH18 transport has the negative all-site phase coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L187-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L187-L235

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

theorem QEC.Distillation.HH18SitewisePhaseInjection.physicalTInv_apply (psi : QubitRegister PhysicalSite)
    (bits : Bitstring PhysicalSite) :
    HH18PuncturedReedMuller.physicalTInv 0 4 psi bits =
      OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
        psi bits := by sorry
