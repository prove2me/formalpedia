-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawAcceptedEndpoint_of_accepts
-- name    : QEC.Distillation.HH18Parameterized.rawAcceptedEndpoint_of_accepts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:45.599987+00:00
-- url     : https://prove2.me/theorems/12940913-b6cb-420c-a95a-1ea9fe676957
-- title:
--   HH18 Parameterized: raw Accepted Endpoint of accepts
-- statement:
--   An accepted physical-error word retains its complete raw operator at the
--   accepted coarse endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L207-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L207-L212

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

theorem QEC.Distillation.HH18Parameterized.rawAcceptedEndpoint_of_accepts {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (haccept : Accepts w r m error) :
    rawAcceptedEndpoint h error outcomes = errorBranchOperator h hdegree error := by sorry
