-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_prepareMeasuredResources_noisyResources_matrixEntry
-- name    : QEC.Distillation.HH18Parameterized.prepareMeasuredResources_noisyResources_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:59:49.89104+00:00
-- url     : https://prove2.me/theorems/0ffd4767-99dd-470b-931b-00beea4e8a75
-- title:
--   HH18 Parameterized: prepare Measured Resources noisy Resources matrix Entry
-- statement:
--   The measured-register mixture itself has the same diagonal Bernoulli
--   matrix entries, without unfolding a concrete error-word enumeration.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L240-L282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L240-L282

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

theorem QEC.Distillation.HH18Parameterized.prepareMeasuredResources_noisyResources_matrixEntry
    (m w : Nat) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (left right : Bitstring (PhysicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex left)
        ((prepareMeasuredResources m w (noisyResources m w epsilon)).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (PhysicalSite m w)) Complex right)) =
      if left = right then
        (HH18NoisyInput.errorWordWeight epsilon
          (bitstringWordEquiv (PhysicalSite m w) left) : Complex)
      else 0 := by sorry
