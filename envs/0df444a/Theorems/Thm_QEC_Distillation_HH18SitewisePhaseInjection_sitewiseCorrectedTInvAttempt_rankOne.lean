-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_sitewiseCorrectedTInvAttempt_rankOne
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:54:18.549281+00:00
-- url     : https://prove2.me/theorems/9e510a42-1fb1-4291-9803-4a4e089984ae
-- title:
--   HH18 Sitewise Phase Injection: sitewise Corrected TInv Attempt rank One
-- statement:
--   The finite branch scalar cancels exactly in the rank-one pure-density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L328-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L328-L342

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

theorem QEC.Distillation.HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_rankOne
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    (InnerProductSpace.rankOne Complex
      (sitewiseCorrectedTInvAttempt error outcomes
        HH18NoisyInput.hh18EncodedLogicalPlusInput)
      (sitewiseCorrectedTInvAttempt error outcomes
        HH18NoisyInput.hh18EncodedLogicalPlusInput)).toLinearMap =
    (InnerProductSpace.rankOne Complex
      (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)
      (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)).toLinearMap := by sorry
