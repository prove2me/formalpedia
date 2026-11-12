-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:22:05.771051+00:00
-- url     : https://prove2.me/theorems/24646962-be09-4de2-be73-09d21f7b3c49
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Stage selected Enough Branch Operator eq
-- statement:
--   The selected output branch may use the compiled routed-history form of the
--   same global unnormalized operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L208-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L208-L222

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w port)
        (decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
          h hdegree epsilon z q stage hstage port rhoUnit) := by sorry
