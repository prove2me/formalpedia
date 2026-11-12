-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_sitewiseCorrectedTInvAttempt_apply
-- name    : QEC.Distillation.HH18Parameterized.sitewiseCorrectedTInvAttempt_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:56:40.1032+00:00
-- url     : https://prove2.me/theorems/e69c9839-c64d-42ba-a63a-6ecf4324343c
-- title:
--   HH18 Parameterized: sitewise Corrected TInv Attempt apply
-- statement:
--   Coordinate formula for the full tensor lift before identifying the HH18
--   target branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L238-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L238-L257

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

theorem QEC.Distillation.HH18Parameterized.sitewiseCorrectedTInvAttempt_apply {m w : Nat}
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w)
    (psi : PhysicalRegister m w) (bits : Bitstring (PhysicalSite m w)) :
    sitewiseCorrectedTInvAttempt error outcomes psi bits =
      sitewiseTInvGlobalPhase error outcomes *
        Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits *
          OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle *
              (HammingWeight
                (PauliSymplectic.bitstringWordEquiv (PhysicalSite m w) bits) : Real)) *
            psi bits := by sorry
