-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:43:35.854867+00:00
-- url     : https://prove2.me/theorems/843daa4c-128e-419c-8823-a3a2d20d3296
-- title:
--   HH18 Parameterized: decoded Retry Pool Accepted Port Successor Born Weight eq tensor Power Born Product
-- statement:
--   The actual routed successor history has precisely the Born product at the
--   selected port's derived next-input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L598-L630
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L598-L630

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)) :
    decodedRetryPoolAcceptedPortSuccessorBornWeight
        h hdegree epsilon z q stage hstage port hhalf rhoUnit history =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w
          (noisyResources m w
            (selectedLogicalPortNextInputRate
              h hdegree epsilon port hhalf)))
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) history := by sorry
