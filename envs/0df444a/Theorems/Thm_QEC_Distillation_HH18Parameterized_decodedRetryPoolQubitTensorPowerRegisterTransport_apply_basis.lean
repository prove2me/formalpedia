-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitTensorPowerRegisterTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerRegisterTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:27:49.577348+00:00
-- url     : https://prove2.me/theorems/abc8bb9b-fdb2-482e-8d84-62a0c4be8f19
-- title:
--   HH18 Parameterized: decoded Retry Pool Qubit Tensor Power Register Transport apply basis
-- statement:
--   The register transport used for one physical block preserves the named
--   recursive computational basis without exposing its finite enumeration.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L91-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L91-L100

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitTensorPowerRegisterTransport_apply_basis
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (history : tensorPowerHistory (Fin 2) (Fintype.card ι)) :
    decodedRetryPoolQubitTensorPowerRegisterTransport ι
        (tensorPowerBasis (EuclideanSpace.basisFun (Fin 2) Complex)
          (Fintype.card ι) history) =
      EuclideanSpace.basisFun (Bitstring ι) Complex
        (decodedRetryPoolQubitTensorPowerBitstringEquiv ι history) := by sorry
