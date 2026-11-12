-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchActualOutputError_exists_coordinate
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchActualOutputError_exists_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T23:00:17.977805+00:00
-- url     : https://prove2.me/theorems/19e11dea-ecd2-4c73-adb0-dfe28c940591
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Actual Output Error exists coordinate
-- statement:
--   The actual finite maximum is attained at one physical terminal coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L79-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L79-L103

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchActualOutputError_exists_coordinate
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∃ coordinate : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth,
      decodedRetryPoolPhysicalExactBatchActualOutputError
          h hdegree epsilon depth rhoUnit =
        decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
          (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
          (Nat.succ_pos depth) coordinate
          (decodedRetryPoolPhysicalExactBatchRun
            h hdegree epsilon depth rhoUnit).acceptedOutput := by sorry
