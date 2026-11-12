-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:20:27.030888+00:00
-- url     : https://prove2.me/theorems/ad6de607-1124-4d65-8e72-9e201613978b
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Coordinate Branch Route Transport apply basis
-- statement:
--   The exact composite successor transport sends a retained-coordinate basis
--   vector to its literal recursive physical-register label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L368-L417
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L368-L417

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (bits : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchRouteTransport
        m w z q stage hstage
        (decodedRetryPoolSuccessorCoordinateTensorBasisVector
          m w z q stage port bits) =
      decodedRetryPoolSuccessorCoordinateBranchBasisVector
        m w z q stage hstage port bits := by sorry
