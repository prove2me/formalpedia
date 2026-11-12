-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateTensorChannel_mapDensity_product
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateTensorChannel_mapDensity_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:19:37.784468+00:00
-- url     : https://prove2.me/theorems/a79c4b4b-994a-40ff-846c-ed31f4b4d0d4
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Coordinate Tensor Channel map Density product
-- statement:
--   The coordinate-tensor stage maps a genuine product of parent blocks to
--   the recursive product of their actual coordinate marginals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L126-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L126-L162

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateTensorChannel_mapDensity_product
    (m w z q : Nat) (stage : Fin z) (port : LogicalSite m w)
    (rho : DensityOperator (LogicalRegister m w))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorCoordinateTensorChannel
      m w z q stage port).mapDensity
        (tensorPowerRegisterProductDensity (LogicalSite m w) rho rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      tensorPowerProductInput
        ((decodedRetryPoolQubitRegisterCoordinateChannel
          (LogicalSite m w) port).mapDensity rho)
        rhoUnit (decodedRetryPoolBackwardSchedule m w z q stage) := by sorry
