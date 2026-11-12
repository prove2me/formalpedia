-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRootInputTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRootInputTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:06:22.865911+00:00
-- url     : https://prove2.me/theorems/b34a0053-0afc-4aeb-adb2-3ea778ca314f
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Root Input Transport apply basis
-- statement:
--   The root transport acts by the exact tensor-history/physical-coordinate
--   reindex on every computational basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Accounting.lean#L119-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Accounting.lean#L119-L133

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRootInputTransport_apply_basis
    (m w z q : Nat) (hz : 0 < z)
    (history : tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)) :
    decodedRetryPoolPhysicalProtocolRootInputTransport m w z q hz
      (tensorPowerBasis
        (EuclideanSpace.basisFun (Qubit.Bitstring (PhysicalSite m w)) Complex)
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolBackwardRootRawCarrier m w z q hz)) Complex
        (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
          (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history) := by sorry
