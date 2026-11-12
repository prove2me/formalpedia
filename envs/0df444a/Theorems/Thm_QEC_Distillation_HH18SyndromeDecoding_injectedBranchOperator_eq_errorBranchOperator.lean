-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_injectedBranchOperator_eq_errorBranchOperator
-- name    : QEC.Distillation.HH18SyndromeDecoding.injectedBranchOperator_eq_errorBranchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:47:44.316653+00:00
-- url     : https://prove2.me/theorems/948ad0bc-6e27-4fc5-84bd-7842e9b167cf
-- title:
--   HH18 Syndrome Decoding: injected Branch Operator eq error Branch Operator
-- statement:
--   Sitewise phase cancellation identifies the injected operator with its Z-error branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L149-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L149-L153

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

theorem QEC.Distillation.HH18SyndromeDecoding.injectedBranchOperator_eq_errorBranchOperator
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    injectedBranchOperator error outcomes = errorBranchOperator error := by sorry
