-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_errorWordBasisDensity_matrixEntry
-- name    : QEC.Distillation.HH18Parameterized.errorWordBasisDensity_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:00:01.104276+00:00
-- url     : https://prove2.me/theorems/2e050671-07c4-46df-bcd1-a4a9a97d96c9
-- title:
--   HH18 Parameterized: error Word Basis Density matrix Entry
-- statement:
--   A recorded physical error word is the corresponding computational-basis
--   rank-one projector, expressed only through Kronecker deltas.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L213-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean#L213-L236

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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

theorem QEC.Distillation.HH18Parameterized.errorWordBasisDensity_matrixEntry
    (m w : Nat) (error : PhysicalErrorWord m w)
    (left right : Bitstring (PhysicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun (Bitstring (PhysicalSite m w)) Complex left)
        ((errorWordBasisDensity m w error).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (PhysicalSite m w)) Complex right)) =
      (if (bitstringWordEquiv (PhysicalSite m w)).symm error = right
        then 1 else 0) *
      (if left = (bitstringWordEquiv (PhysicalSite m w)).symm error
        then 1 else 0) := by sorry
