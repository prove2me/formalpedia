-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateBranchChannel_mapDensity_product
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchChannel_mapDensity_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:21:30.202402+00:00
-- url     : https://prove2.me/theorems/878902b4-9ae5-404b-9f82-dc49b1520f46
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Coordinate Branch Channel map Density product
-- statement:
--   On a genuine product of parent-block densities, the physical fixed-port
--   channel produces the tensor product of their true coordinate marginals and
--   then applies only the exact successor-slot and recursive-register transports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L168-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L168-L192

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchChannel_mapDensity_product
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) (rho : DensityOperator (LogicalRegister m w))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorCoordinateBranchChannel
      m w z q stage hstage port).mapDensity
        (tensorPowerRegisterProductDensity (LogicalSite m w) rho rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      (tensorPowerQubitRegisterTransport (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm.conjDensity
        ((decodedRetryPoolSuccessorPortRecordTransport
          m w z q stage hstage).conjDensity
          ((decodedRetryPoolQubitTensorPowerFinRegisterTransport
            (decodedRetryPoolBackwardSchedule m w z q stage)).conjDensity
            (tensorPowerProductInput
              ((decodedRetryPoolQubitRegisterCoordinateChannel
                (LogicalSite m w) port).mapDensity rho)
              rhoUnit (decodedRetryPoolBackwardSchedule m w z q stage)))) := by sorry
