-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateBranchChannel_rankOne_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:22:13.359365+00:00
-- url     : https://prove2.me/theorems/0d6e5daa-0a14-4492-8507-709267018275
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Coordinate Branch Channel rank One basis
-- statement:
--   On a computational matrix unit, the direct fixed-port channel contracts
--   precisely the sibling logical coordinates and retains the nominated port at
--   every parent-block index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L442-L462
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L442-L462

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchChannel m w z q stage hstage port
        (decodedRetryPoolSuccessorSourceMatrixUnit
          m w z q stage left right) =
      decodedRetryPoolSuccessorCoordinateBranchCoefficient
          m w z q stage port left right •
        decodedRetryPoolSuccessorCoordinateBranchMatrixUnit
          m w z q stage hstage port left right := by sorry
