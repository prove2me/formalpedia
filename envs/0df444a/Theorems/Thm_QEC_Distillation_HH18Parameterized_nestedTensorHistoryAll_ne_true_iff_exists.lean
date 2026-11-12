-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_nestedTensorHistoryAll_ne_true_iff_exists
-- name    : QEC.Distillation.HH18Parameterized.nestedTensorHistoryAll_ne_true_iff_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:19:09.028481+00:00
-- url     : https://prove2.me/theorems/f817d1b6-ea44-491d-9075-d6c9bda7fc7a
-- title:
--   HH18 Parameterized: nested Tensor History All ne true iff exists
-- statement:
--   Failure of the nested Boolean conjunction is witnessed by one actual leaf
--   path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L154-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L154-L172

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

theorem QEC.Distillation.HH18Parameterized.nestedTensorHistoryAll_ne_true_iff_exists {alpha : Type*}
    (predicate : alpha -> Bool) (branches depth : Nat)
    (history : nestedTensorHistory alpha branches depth) :
    nestedTensorHistoryAll predicate branches depth history ≠ true ↔
      ∃ path : nestedTensorPath branches depth,
        predicate (nestedTensorHistoryAt alpha branches depth history path) ≠ true := by sorry
