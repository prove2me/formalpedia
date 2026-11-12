-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_nestedTensorHistoryAll_eq_true_iff
-- name    : QEC.Distillation.HH18Parameterized.nestedTensorHistoryAll_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:57:57.659292+00:00
-- url     : https://prove2.me/theorems/933f0f58-c750-4bb8-9d4f-cde9679b909c
-- title:
--   HH18 Parameterized: nested Tensor History All eq true iff
-- statement:
--   The nested Boolean conjunction holds exactly when its predicate holds at
--   every leaf selected by an actual nested tensor path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L98-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L98-L150

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.nestedTensorHistoryAll_eq_true_iff {alpha : Type*}
    (predicate : alpha -> Bool) (branches : Nat) :
    ∀ (depth : Nat) (history : nestedTensorHistory alpha branches depth),
      nestedTensorHistoryAll predicate branches depth history = true ↔
        ∀ path : nestedTensorPath branches depth,
          predicate
            (nestedTensorHistoryAt alpha branches depth history path) = true := by sorry
