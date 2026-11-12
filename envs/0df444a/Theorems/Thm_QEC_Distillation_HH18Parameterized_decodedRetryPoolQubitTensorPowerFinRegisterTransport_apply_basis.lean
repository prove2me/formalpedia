-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:39:06.214546+00:00
-- url     : https://prove2.me/theorems/e155b5a9-9997-4670-bee8-ab53f8de1bd8
-- title:
--   HH18 Parameterized: decoded Retry Pool Qubit Tensor Power Fin Register Transport apply basis
-- statement:
--   The exact-depth transport preserves every recursive computational basis
--   label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L125-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L125-L133

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerFinRegisterTransport_apply_basis
    (required : Nat) (history : tensorPowerHistory (Fin 2) required) :
    decodedRetryPoolQubitTensorPowerFinRegisterTransport required
        (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
          required history) =
      EuclideanSpace.basisFun (Bitstring (Fin required)) Complex
        (decodedRetryPoolQubitTensorPowerFinBitstringEquiv required history) := by sorry
