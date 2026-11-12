-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_sitewiseCorrectedTInvAttempt_eq_zErrorOperator
-- name    : QEC.Distillation.HH18Parameterized.sitewiseCorrectedTInvAttempt_eq_zErrorOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:57:17.956614+00:00
-- url     : https://prove2.me/theorems/cbf4a303-d7a3-419d-ba3c-c53b51e64bf0
-- title:
--   HH18 Parameterized: sitewise Corrected TInv Attempt eq z Error Operator
-- statement:
--   The actual finite corrected injection is the constructed physical
--   error branch, up to its explicit global phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L261-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L261-L271

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

theorem QEC.Distillation.HH18Parameterized.sitewiseCorrectedTInvAttempt_eq_zErrorOperator {w r m : Nat}
    (h : Coding.PuncturedReedMuller.Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h) =
      sitewiseTInvGlobalPhase error outcomes •
        HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree) := by sorry
