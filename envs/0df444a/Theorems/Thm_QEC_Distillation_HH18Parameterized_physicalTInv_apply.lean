-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalTInv_apply
-- name    : QEC.Distillation.HH18Parameterized.physicalTInv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:56:41.485197+00:00
-- url     : https://prove2.me/theorems/deeef3b7-a6c8-4db3-9ac0-1e8b44dacd4d
-- title:
--   HH18 Parameterized: physical TInv apply
-- statement:
--   The inverse physical HH18 transport has the negative all-site phase
--   coordinates on every finite physical-site type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L186-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L186-L234

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

theorem QEC.Distillation.HH18Parameterized.physicalTInv_apply (m w : Nat) (psi : PhysicalRegister m w)
    (bits : Bitstring (PhysicalSite m w)) :
    HH18PuncturedReedMuller.physicalTInv w m psi bits =
      OneQubitMagic.phaseAmplitude
          (HH18PhaseInjection.tInvIdealAngle *
            (HammingWeight
              (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
        psi bits := by sorry
