-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPool_enoughBranch_sum_eq_enoughMass_smul_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPool_enoughBranch_sum_eq_enoughMass_smul_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:00:10.346706+00:00
-- url     : https://prove2.me/theorems/d2c2ab74-7890-4a28-be2e-70be9d9bb7ea
-- title:
--   HH18 Parameterized: decoded Retry Pool enough Branch sum eq enough Mass smul accepted Product
-- statement:
--   Summing every genuinely enough retry-pool branch on the noisy product
--   input gives the measured enough mass times the fixed accepted-product
--   operator.  No branch is normalized in this identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/EnoughBranchSum.lean#L33-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/EnoughBranchSum.lean#L33-L119

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_EnoughBranchSum
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instEnoughBranchSumClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instEnoughBranchSumClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPool_enoughBranch_sum_eq_enoughMass_smul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (attempts required : Nat) :
    (∑ outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome attempts => PUnit,
      if decodedRetryPoolOutcomeEnough attempts required outcome = true then
        (decodedRetryPoolInstrument h hdegree attempts required).branchOperator
          outcome
          (tensorPowerProductInput
            (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
            attempts).toOperator
      else 0) =
      (decodedRetryPoolEnoughMass h hdegree attempts required
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          attempts) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          required).toOperator := by sorry
