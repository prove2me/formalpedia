-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolTerminalRegisterTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolTerminalRegisterTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:06:58.298005+00:00
-- url     : https://prove2.me/theorems/9d14b06a-b893-48e7-bb99-a789590c88ee
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Terminal Register Transport apply basis
-- statement:
--   The terminal transport maps every physical nested computational basis
--   vector to the exact good-output carrier label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Accounting.lean#L159-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Accounting.lean#L159-L178

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolTerminalRegisterTransport_apply_basis
    (m w z q : Nat) (hz : 0 < z)
    (history : nestedTensorHistory
      (Qubit.Bitstring
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
      (logicalOutputCount m w) (z - 1)) :
    decodedRetryPoolPhysicalProtocolTerminalRegisterTransport m w z q hz
      (nestedTensorBasis
        (EuclideanSpace.basisFun
          (Qubit.Bitstring
            (Fin (decodedRetryPoolBackwardSchedule m w z q
              (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
          Complex)
        (logicalOutputCount m w) (z - 1) history) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolBackwardTerminalGoodCarrier m w z q)) Complex
        (decodedRetryPoolPhysicalProtocolTerminalLabelEquiv m w z q hz history) := by sorry
