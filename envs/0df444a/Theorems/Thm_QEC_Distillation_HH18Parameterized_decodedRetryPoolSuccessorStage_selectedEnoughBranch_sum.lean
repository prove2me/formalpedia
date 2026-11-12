-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStage_selectedEnoughBranch_sum
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughBranch_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:23:35.486357+00:00
-- url     : https://prove2.me/theorems/ae7c2dc3-c947-4461-8228-8f14202396ed
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Stage selected Enough Branch sum
-- statement:
--   Retaining one actual enough successor pool while summing all sibling
--   observations yields its measured enough mass times the genuine next accepted
--   product.  The joint routed successor input may be arbitrarily correlated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L286-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/SelectedEnoughBranch.lean#L286-L316

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStage_selectedEnoughBranch_sum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      (decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolSuccessorStageSelectedNextInput
          h hdegree epsilon z q stage hstage port hhalf rhoUnit) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree
          (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)
          rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)).toOperator := by sorry
