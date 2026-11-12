-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateBranchRouteChannel_rankOne_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:20:35.445537+00:00
-- url     : https://prove2.me/theorems/324ef401-6ef4-45f9-84ff-fb3c579ee4ab
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Coordinate Branch Route Channel rank One basis
-- statement:
--   The exact successor-slot route maps the tensorized fixed-port matrix unit
--   to the corresponding literal recursive next-pool matrix unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L421-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L421-L437

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteChannel_rankOne_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchRouteChannel m w z q stage hstage
        (decodedRetryPoolSuccessorCoordinateTensorMatrixUnit
          m w z q stage port left right) =
      decodedRetryPoolSuccessorCoordinateBranchMatrixUnit
        m w z q stage hstage port left right := by sorry
