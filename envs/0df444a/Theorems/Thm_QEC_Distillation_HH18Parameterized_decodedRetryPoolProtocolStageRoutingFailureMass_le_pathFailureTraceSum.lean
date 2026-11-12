-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolStageRoutingFailureMass_le_pathFailureTraceSum
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolStageRoutingFailureMass_le_pathFailureTraceSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:28:24.809618+00:00
-- url     : https://prove2.me/theorems/337e46f1-e846-48ae-ad53-8a9149c0552d
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Stage Routing Failure Mass le path Failure Trace Sum
-- statement:
--   The actual global stage-routing failure mass is bounded by a sum of local
--   successor-stage failure traces on the genuine unnormalized predecessor-path
--   operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean#L62-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageFailurePathBound.lean#L62-L147

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolStageRoutingFailureMass_le_pathFailureTraceSum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolStageRoutingFailureMass
        h hdegree z q hz stage hstage rho <=
      ∑ path : nestedTensorPath (logicalOutputCount m w) stage,
        decodedRetryPoolProtocolPathFailureTraceAux
          h hdegree z q hz stage hstage path rho := by sorry
