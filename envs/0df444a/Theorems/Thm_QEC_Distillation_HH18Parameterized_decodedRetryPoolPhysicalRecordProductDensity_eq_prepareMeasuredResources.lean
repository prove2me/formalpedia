-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalRecordProductDensity_eq_prepareMeasuredResources
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalRecordProductDensity_eq_prepareMeasuredResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:01:02.373008+00:00
-- url     : https://prove2.me/theorems/dc7609f2-a89c-45ee-8b9c-1c46acb7083b
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Record Product Density eq prepare Measured Resources
-- statement:
--   A genuine product of successor records is exactly the measured physical
--   input density consumed by the next HH18 block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L286-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L286-L304

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalRecordProductDensity_eq_prepareMeasuredResources
    (m w : Nat) (parameter : ErrorParameter)
    (hhalf : parameter.rate ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalRecordProductDensity m w parameter rhoUnit =
      prepareMeasuredResources m w
        (noisyResources m w
          (decodedRetryPoolDiagonalErrorRate parameter hhalf)) := by sorry
