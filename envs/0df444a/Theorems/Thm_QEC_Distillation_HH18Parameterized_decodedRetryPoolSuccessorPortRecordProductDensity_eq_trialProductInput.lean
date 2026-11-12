-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorPortRecordProductDensity_eq_trialProductInput
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortRecordProductDensity_eq_trialProductInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:41:58.571727+00:00
-- url     : https://prove2.me/theorems/5cc946e5-a221-4518-a1d6-d0d7537b5f5c
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Port Record Product Density eq trial Product Input
-- statement:
--   After routing, every next-stage trial block is the exact measured-resource
--   input density at the fixed selected-port error parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L400-L478
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L400-L478

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortRecordProductDensity_eq_trialProductInput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorPortRecordProductDensity
        m w z q stage hstage
        (selectedLogicalPortRawParameter h hdegree epsilon port) rhoUnit =
      tensorPowerRegisterProductDensity (PhysicalSite m w)
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) := by sorry
