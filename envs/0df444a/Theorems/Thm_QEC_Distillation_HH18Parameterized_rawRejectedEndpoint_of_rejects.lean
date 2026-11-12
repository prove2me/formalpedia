-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawRejectedEndpoint_of_rejects
-- name    : QEC.Distillation.HH18Parameterized.rawRejectedEndpoint_of_rejects
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:00:38.63352+00:00
-- url     : https://prove2.me/theorems/045a1c4e-37ad-4c01-8df6-789b6cd50c68
-- title:
--   HH18 Parameterized: raw Rejected Endpoint of rejects
-- statement:
--   A rejected physical-error word retains its complete raw operator in the
--   rejected coarse endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L244-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L244-L255

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

theorem QEC.Distillation.HH18Parameterized.rawRejectedEndpoint_of_rejects {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (hreject : ¬ Accepts w r m error) :
    rawRejectedEndpoint h error outcomes = errorBranchOperator h hdegree error := by sorry
