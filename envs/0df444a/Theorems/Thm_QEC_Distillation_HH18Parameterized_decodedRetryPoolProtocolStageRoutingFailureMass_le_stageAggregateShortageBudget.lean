-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolStageRoutingFailureMass_le_stageAggregateShortageBudget
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolStageRoutingFailureMass_le_stageAggregateShortageBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:27:50.641379+00:00
-- url     : https://prove2.me/theorems/539ec447-5e85-42f8-91ea-b6489678ef14
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Stage Routing Failure Mass le stage Aggregate Shortage Budget
-- statement:
--   The literal global predecessor-success/new-stage-failure mass is bounded
--   by the existing aggregate physical shortage budget at the appended stage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean#L314-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean#L314-L361

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolStageRoutingFailureMass_le_stageAggregateShortageBudget
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolProtocolStageRoutingFailureMass
        h hdegree z q hz stage hstage
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) ≤
      decodedRetryPoolStageAggregateShortageBudget
        w r m epsilon (stage + 1) := by sorry
