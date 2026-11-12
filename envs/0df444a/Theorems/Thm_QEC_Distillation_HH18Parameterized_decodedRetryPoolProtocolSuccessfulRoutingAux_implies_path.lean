-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingAux_implies_path
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_implies_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:05:04.836026+00:00
-- url     : https://prove2.me/theorems/5893babc-10a6-4ca6-9091-e26bea575971
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Successful Routing Aux implies path
-- statement:
--   Global successful routing implies successful routing on every actual
--   logical-port path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/SuccessEvent.lean#L83-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/SuccessEvent.lean#L83-L126

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_implies_path
    (m w z q stage : Nat) (hstage : stage < z)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage hstage)
    (hglobal : decodedRetryPoolProtocolSuccessfulRoutingAux
      m w z q stage hstage outcome = true)
    (path : routedDepthOutputSlots m w stage) :
    decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q stage hstage path outcome = true := by sorry
