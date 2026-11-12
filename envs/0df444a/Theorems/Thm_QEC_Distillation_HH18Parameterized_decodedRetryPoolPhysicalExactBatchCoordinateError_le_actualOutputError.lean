-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchCoordinateError_le_actualOutputError
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchCoordinateError_le_actualOutputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T23:01:03.366586+00:00
-- url     : https://prove2.me/theorems/528ed663-ffd4-41bb-9edc-54d38893c347
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Coordinate Error le actual Output Error
-- statement:
--   Every literal terminal coordinate participates in the reached maximum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L54-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L54-L76

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchCoordinateError_le_actualOutputError
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) :
    decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput <=
      decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit := by sorry
