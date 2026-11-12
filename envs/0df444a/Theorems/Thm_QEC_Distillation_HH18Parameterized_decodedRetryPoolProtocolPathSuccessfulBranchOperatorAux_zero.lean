-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:09:28.698201+00:00
-- url     : https://prove2.me/theorems/1babd151-5954-4a62-95ee-3226597863ee
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successful Branch Operator Aux zero
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Protocol Path Successful Branch Operator Aux zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L413-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L413-L423

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) (path : routedDepthOutputSlots m w 0) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
        h hdegree z q hz rho 0 hz path =
      decodedRetryPoolProtocolRootSuccessfulBranchOperator
        h hdegree z q hz rho := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero
