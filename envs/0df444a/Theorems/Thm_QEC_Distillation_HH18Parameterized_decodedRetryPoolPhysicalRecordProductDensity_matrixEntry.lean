-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalRecordProductDensity_matrixEntry
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalRecordProductDensity_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:30:33.247024+00:00
-- url     : https://prove2.me/theorems/5aaa178a-314f-4dcb-bc60-f36eea49c6f7
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Record Product Density matrix Entry
-- statement:
--   Computational entries of the actual physical record product are diagonal
--   with the exact Bernoulli word weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L116-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L116-L209

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalRecordProductDensity_matrixEntry
    (m w : Nat) (parameter : ErrorParameter)
    (hhalf : parameter.rate ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (left right : Bitstring (PhysicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex left)
        ((decodedRetryPoolPhysicalRecordProductDensity m w parameter rhoUnit).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (PhysicalSite m w)) Complex right)) =
      if left = right then
        (HH18NoisyInput.errorWordWeight
          (decodedRetryPoolDiagonalErrorRate parameter hhalf)
          (bitstringWordEquiv (PhysicalSite m w) left) : Complex)
      else 0 := by sorry
