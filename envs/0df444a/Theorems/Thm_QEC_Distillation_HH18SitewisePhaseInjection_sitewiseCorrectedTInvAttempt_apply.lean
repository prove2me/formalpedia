-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_sitewiseCorrectedTInvAttempt_apply
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:53:51.481795+00:00
-- url     : https://prove2.me/theorems/b41b6468-08d5-45ba-98f8-512bda6ae917
-- title:
--   HH18 Sitewise Phase Injection: sitewise Corrected TInv Attempt apply
-- statement:
--   Coordinate formula for the full tensor lift before identifying the HH18 target branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L238-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L238-L257

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

theorem QEC.Distillation.HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_apply
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (psi : QubitRegister PhysicalSite) (bits : Bitstring PhysicalSite) :
    sitewiseCorrectedTInvAttempt error outcomes psi bits =
      sitewiseTInvGlobalPhase error outcomes *
        Qubit.zSupportPhase (PauliSymplectic.binarySupport error) bits *
          OneQubitMagic.phaseAmplitude
            (HH18PhaseInjection.tInvIdealAngle *
              (HammingWeight
                (PauliSymplectic.bitstringWordEquiv PhysicalSite bits) : Real)) *
            psi bits := by sorry
