-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq_local
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:23:23.960661+00:00
-- url     : https://prove2.me/theorems/cb8d47ac-7e34-4c58-a890-053e8e25b5c6
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Stage selected Enough Branch Operator eq local
-- statement:
--   Retaining the selected output coordinate after the routed global sum
--   leaves the local enough-event branch sum on the true input marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L250-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L250-L281

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq_local
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      decodedRetryPoolSuccessorStageLocalEnoughOperator h hdegree z q stage hstage
        (tensorPowerCoordinateOperator (logicalOutputCount m w)
          (decodedRetryPoolLogicalSiteFinEquiv m w port)
          (decodedRetryPoolSuccessorStageJointInput
            h hdegree epsilon z q stage hstage rhoUnit).toOperator) := by sorry
