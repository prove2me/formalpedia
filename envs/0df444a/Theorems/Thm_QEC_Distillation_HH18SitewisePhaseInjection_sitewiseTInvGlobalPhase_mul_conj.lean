-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_sitewiseTInvGlobalPhase_mul_conj
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.sitewiseTInvGlobalPhase_mul_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:54:49.969284+00:00
-- url     : https://prove2.me/theorems/3dc81700-2e9c-490e-ba68-1b31be9c7a4c
-- title:
--   HH18 Sitewise Phase Injection: sitewise TInv Global Phase mul conj
-- statement:
--   The explicit finite product scalar has unit modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L298-L308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L298-L308

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

theorem QEC.Distillation.HH18SitewisePhaseInjection.sitewiseTInvGlobalPhase_mul_conj
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    sitewiseTInvGlobalPhase error outcomes *
      star (sitewiseTInvGlobalPhase error outcomes) = 1 := by sorry
