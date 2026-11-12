-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathFailureTraceAux_le_portShortageSum
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathFailureTraceAux_le_portShortageSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:28:19.836265+00:00
-- url     : https://prove2.me/theorems/d42502f5-b494-44a7-b3d2-aeb37988065b
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Failure Trace Aux le port Shortage Sum
-- statement:
--   On the genuine noisy root input, one routed-path failure trace is bounded
--   by the true shortage masses of the physical successor pools at that path's
--   reached rate.  The predecessor branch remains unnormalized; its mass is
--   dropped only using the proved physical probability bound `mass ≤ 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean#L153-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean#L153-L219

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathFailureTraceAux_le_portShortageSum
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
      ∑ port : LogicalSite m w,
        decodedRetryPoolShortageMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage
              (decodedRetryPoolNestedPathEquiv m w stage path))
            z q ⟨stage, by omega⟩ hstage port
            (routedDepthPathNextHalf h hdegree epsilon hsmall
              (decodedRetryPoolNestedPathEquiv m w stage path) port)
            rhoUnit) := by sorry
