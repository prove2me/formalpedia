-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_rawSyndromeBranch_eq
-- name    : QEC.Distillation.HH18SyndromeDecoding.rawSyndromeBranch_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:43:10.996599+00:00
-- url     : https://prove2.me/theorems/3c640253-1a56-44e3-a758-cbf4b8e0447f
-- title:
--   HH18 Syndrome Decoding: raw Syndrome Branch eq
-- statement:
--   The full instrument selects precisely the syndrome derived from the Z-error word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L323-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L323-L348

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

theorem QEC.Distillation.HH18SyndromeDecoding.rawSyndromeBranch_eq
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (syndrome : Syndrome) :
    rawSyndromeBranch error outcomes syndrome =
      if syndrome = measuredSyndrome error then
        errorBranchOperator error
      else
        0 := by sorry
