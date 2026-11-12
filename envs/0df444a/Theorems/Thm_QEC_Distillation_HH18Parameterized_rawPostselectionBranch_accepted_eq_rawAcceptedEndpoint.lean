-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint
-- name    : QEC.Distillation.HH18Parameterized.rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:36.699304+00:00
-- url     : https://prove2.me/theorems/0baffdcc-0359-46c6-9cb4-0ebaf335f888
-- title:
--   HH18 Parameterized: raw Postselection Branch accepted eq raw Accepted Endpoint
-- statement:
--   Coarse acceptance retains exactly the all-positive raw syndrome endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L164-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L164-L179

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Parameterized.rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) :
    rawPostselectionBranch h .accepted (injectedBranchOperator h error outcomes) =
      rawAcceptedEndpoint h error outcomes := by sorry
