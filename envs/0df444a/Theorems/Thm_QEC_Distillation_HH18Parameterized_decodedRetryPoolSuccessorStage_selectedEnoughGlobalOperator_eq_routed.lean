-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStage_selectedEnoughGlobalOperator_eq_routed
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughGlobalOperator_eq_routed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:22:14.878473+00:00
-- url     : https://prove2.me/theorems/6ccd5c66-4ef6-450b-898c-994f4de9ae57
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Stage selected Enough Global Operator eq routed
-- statement:
--   The channel-first physical successor sum is exactly its routed
--   tensor-history form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L159-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L159-L187

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_EnoughBranchSum
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Branches_ChannelFirstFilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughGlobalOperator_eq_routed
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
        h hdegree epsilon z q stage hstage port rhoUnit := by sorry
