-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawRejectedEndpoint_of_accepts
-- name    : QEC.Distillation.HH18Parameterized.rawRejectedEndpoint_of_accepts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:00:31.8962+00:00
-- url     : https://prove2.me/theorems/7664e63d-2d50-449a-8503-6a049fc2ab01
-- title:
--   HH18 Parameterized: raw Rejected Endpoint of accepts
-- statement:
--   An accepted physical-error word contributes no raw mass to the rejected
--   coarse endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L224-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L224-L240

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

theorem QEC.Distillation.HH18Parameterized.rawRejectedEndpoint_of_accepts {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (haccept : Accepts w r m error) :
    rawRejectedEndpoint h error outcomes = 0 := by sorry
