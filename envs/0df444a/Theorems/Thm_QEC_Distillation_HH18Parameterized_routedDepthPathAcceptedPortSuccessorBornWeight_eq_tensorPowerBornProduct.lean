-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:57:05.958024+00:00
-- url     : https://prove2.me/theorems/ff57aecf-fbac-4986-8edb-ffabb3fac76f
-- title:
--   HH18 Parameterized: routed Depth Path Accepted Port Successor Born Weight eq tensor Power Born Product
-- statement:
--   The observed history mass on that actual successor input is the tensor
--   product of the one-level accepted/rejected Born weights at the appended path
--   rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L95-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L95-L127

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
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
        ⟨stage.1 + 1, hstage⟩)) :
    decodedRetryPoolAcceptedPortSuccessorBornWeight h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall depth path)
        z q stage hstage port
        (routedDepthPathNextHalf h hdegree epsilon hsmall path port)
        rhoUnit history =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w
          (noisyResources m w
            (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
              (routedDepthOutputPathAppend m w depth path port))))
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) history := by sorry
