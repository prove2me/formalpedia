-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:56:43.190582+00:00
-- url     : https://prove2.me/theorems/13c90edb-0708-4bc8-a847-4879c8f82fad
-- title:
--   HH18 Parameterized: routed Depth Path Accepted Port Successor Conditional Density eq accepted Product
-- statement:
--   When the observed successor history is large enough and has positive
--   mass, normalizing its actual branch yields the accepted-product density at
--   the appended path rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L132-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L132-L183

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
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
      decodedRetryPoolAcceptedPortSuccessorBornWeight h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall depth path)
        z q stage hstage port
        (routedDepthPathNextHalf h hdegree epsilon hsmall path port)
        rhoUnit history) :
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩)).conditionalDensity
        ⟨history, PUnit.unit⟩
        ((decodedRetryPoolAcceptedPortSuccessorInputChannel
          m w z q stage hstage port).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree
              (routedDepthPathRate h hdegree epsilon hsmall depth path)
              rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage)))
        hpositive =
      decodedRetryPoolAcceptedProductDensity h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
          (routedDepthOutputPathAppend m w depth path port))
        rhoUnit
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩) := by sorry
