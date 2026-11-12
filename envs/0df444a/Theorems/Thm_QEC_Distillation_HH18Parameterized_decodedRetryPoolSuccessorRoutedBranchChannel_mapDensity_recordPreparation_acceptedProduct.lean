-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRoutedBranchChannel_mapDensity_recordPreparation_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchChannel_mapDensity_recordPreparation_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:22:14.438647+00:00
-- url     : https://prove2.me/theorems/0dfd020b-32d9-4560-9bb2-ce5223ab726b
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Routed Branch Channel map Density record Preparation accepted Product
-- statement:
--   On the genuine accepted-parent product, the actual global physical route
--   (sitewise record preparation, full successor reindexing/regrouping, then one
--   outer-branch marginal) supplies exactly the literal product input consumed by
--   the corresponding immediate-successor retry pool.  No independence between
--   distinct logical ports of one accepted parent block is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L729-L785
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L729-L785

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchChannel_mapDensity_recordPreparation_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorRoutedBranchChannel m w z q stage hstage
      (decodedRetryPoolLogicalSiteFinEquiv m w port)).mapDensity
        ((decodedRetryPoolSuccessorRecordPreparationChannel
          m w z q stage).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage))) =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by sorry
