-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessorEnoughOperator_smul
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessorEnoughOperator_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:26:43.287094+00:00
-- url     : https://prove2.me/theorems/52bdb32c-ddbc-43dc-8bbe-be1cce5281f3
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successor Enough Operator smul
-- statement:
--   The arbitrary-input selected successor operator is complex-linear.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L286-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L286-L311

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessorEnoughOperator_smul
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q stage : Nat) (hstage : stage + 1 < z)
    (port : LogicalSite m w) (c : Complex)
    (A : Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage, by omega⟩) × LogicalSite m w))) :
    decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage port (c • A) =
      c • decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage port A := by sorry
