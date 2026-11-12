-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatch_physicalPolylogarithmicExpectedYieldOverhead
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatch_physicalPolylogarithmicExpectedYieldOverhead
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T23:01:43.693226+00:00
-- url     : https://prove2.me/theorems/dee99587-1b39-485d-b6fa-2f760766cd5c
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch physical Polylogarithmic Expected Yield Overhead
-- statement:
--   Final dependent adapter: slots, reached errors, and yields all come from
--   the same actual exact-batch physical run at each index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L258-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L258-L285

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatch_physicalPolylogarithmicExpectedYieldOverhead
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (decodedRetryPoolPhysicalExactBatchInputSlots m w)
      (decodedRetryPoolPhysicalExactBatchOutputSlots m w)
      (fun depth =>
        routedDepthScheduleTargetError w r m epsilon (depth + 1))
      (fun depth => decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit)
      (fun depth => decodedRetryPoolPhysicalExactBatchYield
        h hdegree epsilon depth rhoUnit)
      (routedDepthScheduleGamma w r m)
      (decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon) := by sorry
