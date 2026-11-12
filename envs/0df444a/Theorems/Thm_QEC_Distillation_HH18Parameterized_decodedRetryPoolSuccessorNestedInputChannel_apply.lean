-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorNestedInputChannel_apply
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:35:34.847785+00:00
-- url     : https://prove2.me/theorems/57ef21a1-6109-4b73-b98b-85c488de3312
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Nested Input Channel apply
-- statement:
--   The physical handoff is exactly sitewise preparation, reindexing, then
--   regrouping.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L534-L542
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L534-L542

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_apply
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (Qubit.QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage))) :
    decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage A =
      decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage
        (decodedRetryPoolSuccessorReindexChannel m w z q stage hstage
          (decodedRetryPoolSuccessorRecordPreparationChannel m w z q stage A)) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_apply
