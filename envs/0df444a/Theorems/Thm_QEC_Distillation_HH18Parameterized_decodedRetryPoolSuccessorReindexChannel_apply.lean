-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorReindexChannel_apply
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorReindexChannel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:14:32.802182+00:00
-- url     : https://prove2.me/theorems/61132735-e510-4689-acac-902f0dd9572a
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Reindex Channel apply
-- statement:
--   The reindex channel acts by conjugation with the derived basis-preserving
--   unitary transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L223-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L223-L229

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorReindexChannel_apply
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (Qubit.QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage))) :
    decodedRetryPoolSuccessorReindexChannel m w z q stage hstage A =
      (decodedRetryPoolSuccessorRegisterTransport m w z q stage hstage).conjOperator A := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorReindexChannel_apply
