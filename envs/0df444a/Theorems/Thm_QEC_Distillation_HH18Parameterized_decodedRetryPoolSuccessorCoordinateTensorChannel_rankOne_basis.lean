-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateTensorChannel_rankOne_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateTensorChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:20:18.24946+00:00
-- url     : https://prove2.me/theorems/3434d24e-344a-4beb-bade-f4ae8c7f3ae3
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Coordinate Tensor Channel rank One basis
-- statement:
--   The coordinate-tensor stage acts on flat source matrix units by the
--   product of the true one-block coordinate-contraction coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L303-L364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L303-L364

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateTensorChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateTensorChannel m w z q stage port
        (decodedRetryPoolSuccessorSourceMatrixUnit
          m w z q stage left right) =
      decodedRetryPoolSuccessorCoordinateBranchCoefficient
          m w z q stage port left right •
        decodedRetryPoolSuccessorCoordinateTensorMatrixUnit
          m w z q stage port left right := by sorry
