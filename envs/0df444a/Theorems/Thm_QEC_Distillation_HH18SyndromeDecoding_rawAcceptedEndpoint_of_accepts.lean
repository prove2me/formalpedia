-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_rawAcceptedEndpoint_of_accepts
-- name    : QEC.Distillation.HH18SyndromeDecoding.rawAcceptedEndpoint_of_accepts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:45:52.941109+00:00
-- url     : https://prove2.me/theorems/a7595bc8-1dcd-4db6-9d87-b6ce0019eb07
-- title:
--   HH18 Syndrome Decoding: raw Accepted Endpoint of accepts
-- statement:
--   An accepted error word retains its complete raw operator at the accepted endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L368-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L368-L373

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

theorem QEC.Distillation.HH18SyndromeDecoding.rawAcceptedEndpoint_of_accepts
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (haccept : Accepts error) :
    rawAcceptedEndpoint error outcomes = errorBranchOperator error := by sorry
