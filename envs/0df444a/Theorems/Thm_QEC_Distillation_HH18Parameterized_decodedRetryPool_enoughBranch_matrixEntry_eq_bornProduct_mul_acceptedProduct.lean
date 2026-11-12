-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPool_enoughBranch_matrixEntry_eq_bornProduct_mul_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPool_enoughBranch_matrixEntry_eq_bornProduct_mul_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:08:30.378126+00:00
-- url     : https://prove2.me/theorems/4ea78347-b83c-43e6-81b3-2d94b80ead69
-- title:
--   HH18 Parameterized: decoded Retry Pool enough Branch matrix Entry eq born Product mul accepted Product
-- statement:
--   An enough-history physical retry-pool branch matrix entry is exactly its
--   full observed-history Born product times the corresponding entry of the fixed
--   accepted product density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedProduct.lean#L63-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedProduct.lean#L63-L231

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPool_enoughBranch_matrixEntry_eq_bornProduct_mul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (attempts required : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card)
    (left right : Bitstring (Fin required × LogicalSite m w)) :
    inner Complex
        (EuclideanSpace.basisFun
          (Bitstring (Fin required × LogicalSite m w)) Complex left)
        ((decodedRetryPoolInstrument h hdegree attempts required).branchOperator
          ⟨history, PUnit.unit⟩
          (tensorPowerProductInput
            (prepareMeasuredResources m w (noisyResources m w epsilon))
            rhoUnit attempts).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (Fin required × LogicalSite m w)) Complex right)) =
      (tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
        history : Complex) *
      inner Complex
        (EuclideanSpace.basisFun
          (Bitstring (Fin required × LogicalSite m w)) Complex left)
        ((decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          required).toOperator
          (EuclideanSpace.basisFun
            (Bitstring (Fin required × LogicalSite m w)) Complex right)) := by sorry
