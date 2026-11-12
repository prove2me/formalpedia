-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathFailureTraceAux_le_pathBudget
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathFailureTraceAux_le_pathBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:28:24.760094+00:00
-- url     : https://prove2.me/theorems/64e2c8f1-7b08-45e5-b940-eb500c2c4f72
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Failure Trace Aux le path Budget
-- statement:
--   One routed-path failure trace is bounded by one copy of the physical
--   successor-stage envelope budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean#L223-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean#L223-L310

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageFailurePathBound
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instStageFailurePathBoundClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instStageFailurePathBoundClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathFailureTraceAux_le_pathBudget
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (path : nestedTensorPath (logicalOutputCount m w) stage) :
    decodedRetryPoolProtocolPathFailureTraceAux
        h hdegree z q hz stage hstage path
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) ≤
      (logicalOutputCount m w : Real) *
        decodedRetryPoolDyadicDenominator (stage + 1) *
        physicalInputCount m w *
        routedDepthErrorEnvelope w r m epsilon (stage + 1) := by sorry
