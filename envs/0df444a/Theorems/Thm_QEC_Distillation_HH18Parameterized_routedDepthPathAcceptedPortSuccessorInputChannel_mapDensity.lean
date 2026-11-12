-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathAcceptedPortSuccessorInputChannel_mapDensity
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathAcceptedPortSuccessorInputChannel_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:56:10.706336+00:00
-- url     : https://prove2.me/theorems/e636dce1-8e7a-418d-b358-2f00e897f7bc
-- title:
--   HH18 Parameterized: routed Depth Path Accepted Port Successor Input Channel map Density
-- statement:
--   A fixed accepted output port of the actual parent retry pool supplies the
--   literal tensor-product input consumed by the next retry pool on the appended
--   routed path.  This is a marginal statement for one selected port; it does not
--   assume that distinct sibling ports are independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L62-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L62-L90

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathAcceptedPortSuccessorInputChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolAcceptedPortSuccessorInputChannel
      m w z q stage hstage port).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall depth path)
          rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      tensorPowerProductInput
        (prepareMeasuredResources m w
          (noisyResources m w
            (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
              (routedDepthOutputPathAppend m w depth path port))))
        rhoUnit
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) := by sorry
