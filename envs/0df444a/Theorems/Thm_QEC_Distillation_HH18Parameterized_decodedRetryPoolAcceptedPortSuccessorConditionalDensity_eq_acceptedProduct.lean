-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:02:32.50642+00:00
-- url     : https://prove2.me/theorems/ff727b0c-fc42-4109-a192-ad5b11de9aa3
-- title:
--   HH18 Parameterized: decoded Retry Pool Accepted Port Successor Conditional Density eq accepted Product
-- statement:
--   A positive enough immediate-successor history normalizes to the genuine
--   product of selected accepted outputs at the derived next-input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L634-L708
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L634-L708

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩))
    (henough :
      decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩ ≤
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩) history).card)
    (hpositive : 0 <
      decodedRetryPoolAcceptedPortSuccessorBornWeight
        h hdegree epsilon z q stage hstage port hhalf rhoUnit history) :
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩)).conditionalDensity
        ⟨history, PUnit.unit⟩
        ((decodedRetryPoolAcceptedPortSuccessorInputChannel
          m w z q stage hstage port).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage)))
        hpositive =
      decodedRetryPoolAcceptedProductDensity h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)
        rhoUnit
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩) := by sorry
