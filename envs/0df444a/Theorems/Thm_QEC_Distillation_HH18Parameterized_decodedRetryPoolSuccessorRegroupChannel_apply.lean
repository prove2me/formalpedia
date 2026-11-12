-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupChannel_apply
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupChannel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:34:55.696371+00:00
-- url     : https://prove2.me/theorems/fb586acc-a514-4023-bcd3-314f22d1817f
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Regroup Channel apply
-- statement:
--   The regrouping channel acts by conjugation with its basis-preserving
--   unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L235-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L235-L241

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupChannel_apply
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (Qubit.QubitRegister
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))) :
    decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage A =
      (decodedRetryPoolSuccessorRegroupTransport m w z q stage hstage).conjOperator A := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupChannel_apply
