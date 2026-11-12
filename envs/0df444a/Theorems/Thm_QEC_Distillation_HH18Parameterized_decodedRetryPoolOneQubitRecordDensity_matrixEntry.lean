-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolOneQubitRecordDensity_matrixEntry
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolOneQubitRecordDensity_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:30:28.190941+00:00
-- url     : https://prove2.me/theorems/68c0fed2-8708-4278-a1ed-2baa65365d38
-- title:
--   HH18 Parameterized: decoded Retry Pool One Qubit Record Density matrix Entry
-- statement:
--   A one-qubit successor record has the corresponding literal diagonal
--   computational matrix entry.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L43-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L43-L87

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolOneQubitRecordDensity_matrixEntry
    (parameter : ErrorParameter) (hhalf : parameter.rate ≤ 1 / 2)
    (left right : Fin 2) :
    inner Complex (EuclideanSpace.basisFun (Fin 2) Complex left)
        ((decodedRetryPoolOneQubitRecordDensity parameter).toOperator
          (EuclideanSpace.basisFun (Fin 2) Complex right)) =
      if left = right then
        (HH18NoisyInput.bitErrorWeight
          (decodedRetryPoolDiagonalErrorRate parameter hhalf)
          (left : ZMod 2) : Complex)
      else 0 := by sorry
