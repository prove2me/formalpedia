-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_rawRejectedEndpoint_of_accepts
-- name    : QEC.Distillation.HH18SyndromeDecoding.rawRejectedEndpoint_of_accepts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:46:05.739422+00:00
-- url     : https://prove2.me/theorems/2cd5008d-8682-4fa8-b2e8-feb414657532
-- title:
--   HH18 Syndrome Decoding: raw Rejected Endpoint of accepts
-- statement:
--   An accepted error word contributes no raw mass to the rejected endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L384-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L384-L400

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SyndromeDecoding
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18SyndromeDecoding.rawRejectedEndpoint_of_accepts
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (haccept : Accepts error) :
    rawRejectedEndpoint error outcomes = 0 := by sorry
