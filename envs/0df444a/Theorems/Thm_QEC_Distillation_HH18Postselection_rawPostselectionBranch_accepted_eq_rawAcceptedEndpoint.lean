-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Postselection_rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint
-- name    : QEC.Distillation.HH18Postselection.rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:47:01.960847+00:00
-- url     : https://prove2.me/theorems/fb34c805-530c-4c6b-9fbc-0e34148c67b8
-- title:
--   HH18 Postselection: raw Postselection Branch accepted eq raw Accepted Endpoint
-- statement:
--   Coarse acceptance retains exactly the existing all-positive injected endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L137-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L137-L151

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Postselection
open Coding Semantics
open Coding.PauliSymplectic
open HH18SyndromeDecoding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Postselection.rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    rawPostselectionBranch .accepted (injectedBranchOperator error outcomes) =
      rawAcceptedEndpoint error outcomes := by sorry
