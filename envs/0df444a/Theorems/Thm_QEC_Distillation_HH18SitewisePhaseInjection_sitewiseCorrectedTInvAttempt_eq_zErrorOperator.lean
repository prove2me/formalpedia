-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_sitewiseCorrectedTInvAttempt_eq_zErrorOperator
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_eq_zErrorOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:54:07.375189+00:00
-- url     : https://prove2.me/theorems/bd2ee5b2-c796-4c8d-8fd6-89275430308d
-- title:
--   HH18 Sitewise Phase Injection: sitewise Corrected TInv Attempt eq z Error Operator
-- statement:
--   The actual finite corrected-injection register is the existing physical error branch, up to its explicit scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L260-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L260-L272

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

theorem QEC.Distillation.HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_eq_zErrorOperator
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    sitewiseCorrectedTInvAttempt error outcomes
        HH18NoisyInput.hh18EncodedLogicalPlusInput =
      sitewiseTInvGlobalPhase error outcomes •
        HH18NoisyInput.zErrorOperator error
          HH18NoisyInput.hh18PhysicalTInvBranch := by sorry
