-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStageFailureMass_le_portShortageSum
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStageFailureMass_le_portShortageSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:26:28.539205+00:00
-- url     : https://prove2.me/theorems/12fc0be9-5d8c-43b6-8bff-0e7efdd5f79b
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Stage Failure Mass le port Shortage Sum
-- statement:
--   On a genuine accepted-parent product, failure of at least one actual
--   successor retry pool is bounded by the sum of the true per-port shortage
--   masses.  The routed successor input may be correlated across ports; this is
--   the finite-instrument union bound on its actual marginals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean#L72-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean#L72-L193

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStageFailureMass_le_portShortageSum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (hhalf : ∀ port : LogicalSite m w,
      selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : decodedRetryPoolSuccessorStageOutcome
            m w z q stage hstage =>
          decodedRetryPoolSuccessorStageRoutingGood
            m w z q stage hstage outcome ≠ true),
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q stage hstage).bornWeight outcome
          (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q stage))) ≤
      ∑ port : LogicalSite m w,
        decodedRetryPoolShortageMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)
          (tensorPowerProductInput
            (prepareMeasuredResources m w
              (noisyResources m w
                (selectedLogicalPortNextInputRate
                  h hdegree epsilon port (hhalf port))))
            rhoUnit
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage.1 + 1, hstage⟩)) := by sorry
