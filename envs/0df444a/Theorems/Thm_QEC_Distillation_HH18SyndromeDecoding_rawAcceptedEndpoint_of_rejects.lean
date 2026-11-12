-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_rawAcceptedEndpoint_of_rejects
-- name    : QEC.Distillation.HH18SyndromeDecoding.rawAcceptedEndpoint_of_rejects
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:45:49.327913+00:00
-- url     : https://prove2.me/theorems/3c7d11e4-680d-473e-8178-d518969d8fe2
-- title:
--   HH18 Syndrome Decoding: raw Accepted Endpoint of rejects
-- statement:
--   A rejected error word has a literal zero accepted raw endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L376-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L376-L381

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

theorem QEC.Distillation.HH18SyndromeDecoding.rawAcceptedEndpoint_of_rejects
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (hreject : ¬ Accepts error) :
    rawAcceptedEndpoint error outcomes = 0 := by sorry
