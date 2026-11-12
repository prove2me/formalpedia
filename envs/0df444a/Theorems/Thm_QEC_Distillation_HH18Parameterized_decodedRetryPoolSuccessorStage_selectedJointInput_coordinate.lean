-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStage_selectedJointInput_coordinate
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedJointInput_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:22:41.914116+00:00
-- url     : https://prove2.me/theorems/a39f6978-681c-4b42-bc3f-f0de64af47bc
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Stage selected Joint Input coordinate
-- statement:
--   The true selected marginal of the correlated routed successor input is
--   the literal noisy product at that port's next physical rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L76-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L76-L101

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedJointInput_coordinate
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w port)
        (decodedRetryPoolSuccessorStageJointInput
          h hdegree epsilon z q stage hstage rhoUnit).toOperator =
      (decodedRetryPoolSuccessorStageSelectedNextInput
        h hdegree epsilon z q stage hstage port hhalf rhoUnit).toOperator := by sorry
