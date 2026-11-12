-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_rawRejectedEndpoint_of_rejects
-- name    : QEC.Distillation.HH18SyndromeDecoding.rawRejectedEndpoint_of_rejects
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:46:03.370533+00:00
-- url     : https://prove2.me/theorems/9838e091-0bcd-4fcb-bb8a-20f1dbb6766b
-- title:
--   HH18 Syndrome Decoding: raw Rejected Endpoint of rejects
-- statement:
--   A rejected error word retains its complete raw operator in the rejected sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L403-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L403-L414

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

theorem QEC.Distillation.HH18SyndromeDecoding.rawRejectedEndpoint_of_rejects
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (hreject : ¬ Accepts error) :
    rawRejectedEndpoint error outcomes = errorBranchOperator error := by sorry
