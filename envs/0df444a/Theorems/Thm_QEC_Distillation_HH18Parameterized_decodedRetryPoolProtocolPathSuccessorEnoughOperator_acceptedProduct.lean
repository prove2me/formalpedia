-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessorEnoughOperator_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessorEnoughOperator_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:26:52.357717+00:00
-- url     : https://prove2.me/theorems/f7a83ee3-2f0d-453a-a208-6729a99b489c
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successor Enough Operator accepted Product
-- statement:
--   On a genuine accepted predecessor product, the arbitrary-input selected
--   successor operator is the measured next-pool enough mass times the genuine
--   next accepted product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L316-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L316-L343

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessorEnoughOperator_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q stage : Nat) (hstage : stage + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage port
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage, by omega⟩)).toOperator =
      (decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolSuccessorStageSelectedNextInput
          h hdegree epsilon z q ⟨stage, by omega⟩ hstage port hhalf
          rhoUnit) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree
          (selectedLogicalPortNextInputRate
            h hdegree epsilon port hhalf)
          rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)).toOperator := by sorry
