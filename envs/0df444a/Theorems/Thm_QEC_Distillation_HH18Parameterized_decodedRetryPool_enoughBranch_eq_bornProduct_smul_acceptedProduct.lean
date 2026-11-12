-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPool_enoughBranch_eq_bornProduct_smul_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPool_enoughBranch_eq_bornProduct_smul_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:45:10.43398+00:00
-- url     : https://prove2.me/theorems/798a3c2d-780c-4bca-9081-1c006e6700fc
-- title:
--   HH18 Parameterized: decoded Retry Pool enough Branch eq born Product smul accepted Product
-- statement:
--   Operator form of the enough-history identity: the complete physical pool
--   branch is its actual history Born product times the fixed accepted product
--   density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedProduct.lean#L236-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedProduct.lean#L236-L288

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPool_enoughBranch_eq_bornProduct_smul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (attempts required : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card) :
    (decodedRetryPoolInstrument h hdegree attempts required).branchOperator
        ⟨history, PUnit.unit⟩
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          attempts).toOperator =
      (tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
        history : Complex) •
      (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
        required).toOperator := by sorry
