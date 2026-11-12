-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_sitewiseCorrectedTInvAttempt_eq_errorBranch
-- name    : QEC.Distillation.HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_eq_errorBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:54:41.522642+00:00
-- url     : https://prove2.me/theorems/0c10f4cd-3f07-454a-84e0-e1182d4ab2cf
-- title:
--   HH18 Sitewise Phase Injection: sitewise Corrected TInv Attempt eq error Branch
-- statement:
--   Named form of the same equality using the target family from `HH18NoisyInput`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L275-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SitewisePhaseInjection.lean#L275-L282

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

theorem QEC.Distillation.HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_eq_errorBranch
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    sitewiseCorrectedTInvAttempt error outcomes
        HH18NoisyInput.hh18EncodedLogicalPlusInput =
      sitewiseTInvGlobalPhase error outcomes •
        HH18NoisyInput.hh18PhysicalTInvErrorBranch error := by sorry
