-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawPostselectionBranch_rejected_eq_rawRejectedEndpoint
-- name    : QEC.Distillation.HH18Parameterized.rawPostselectionBranch_rejected_eq_rawRejectedEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:27.973188+00:00
-- url     : https://prove2.me/theorems/098ba90c-96d5-4eae-acff-00b2f974794b
-- title:
--   HH18 Parameterized: raw Postselection Branch rejected eq raw Rejected Endpoint
-- statement:
--   Coarse rejection retains exactly the sum of all non-all-positive raw
--   syndrome endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L183-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L183-L203

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

theorem QEC.Distillation.HH18Parameterized.rawPostselectionBranch_rejected_eq_rawRejectedEndpoint {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) :
    rawPostselectionBranch h .rejected (injectedBranchOperator h error outcomes) =
      rawRejectedEndpoint h error outcomes := by sorry
