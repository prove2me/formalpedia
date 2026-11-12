-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortSuccessorRecordChannel_mapDensity
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorRecordChannel_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:02:02.232838+00:00
-- url     : https://prove2.me/theorems/fa0d7e31-0b5a-4dfa-9094-f5f3976583f9
-- title:
--   HH18 Parameterized: decoded Retry Pool Accepted Port Successor Record Channel map Density
-- statement:
--   The complete successor-port channel maps the genuine accepted-parent
--   product to the already-identified routed record product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L219-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L219-L238

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorRecordChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    (decodedRetryPoolAcceptedPortSuccessorRecordChannel
      m w z q stage hstage port).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      decodedRetryPoolSuccessorPortRecordProductDensity
        m w z q stage hstage
        (selectedLogicalPortRawParameter h hdegree epsilon port) rhoUnit := by sorry
