-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_succ
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:27:57.473553+00:00
-- url     : https://prove2.me/theorems/979babf0-e72e-4334-94b0-c05666037ee9
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successful Branch Operator Global Aux succ
-- statement:
--   The original whole-history selected path marginal obeys the same literal
--   successor recurrence as the recursive physical path operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/GlobalBridge.lean#L229-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/GlobalBridge.lean#L229-L278

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_succ
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (path : routedDepthOutputSlots m w (previous.1 + 1))
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz (previous.1 + 1) hstage path rho =
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q previous.1 hstage
          (routedDepthOutputPathLast m w previous.1 path)
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
            h hdegree z q hz previous.1 previous.2
              (routedDepthOutputPathInit m w previous.1 path) rho) := by sorry
