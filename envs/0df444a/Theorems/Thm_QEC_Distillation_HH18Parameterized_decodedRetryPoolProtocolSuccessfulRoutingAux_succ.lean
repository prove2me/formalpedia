-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingAux_succ
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:57:44.787716+00:00
-- url     : https://prove2.me/theorems/fd242203-c25d-40f7-8e36-b84184c154ba
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Successful Routing Aux succ
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Protocol Successful Routing Aux succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L217-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L217-L228

import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_succ
    (m w z q stage : Nat) (hstage : stage + 1 < z)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q (stage + 1) hstage) :
    decodedRetryPoolProtocolSuccessfulRoutingAux
        m w z q (stage + 1) hstage outcome =
      (decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage (by omega) outcome.1 &&
        nestedTensorHistoryAll
          (decodedRetryPoolSuccessorStageRoutingGood
            m w z q ⟨stage, by omega⟩ hstage)
          (logicalOutputCount m w) stage outcome.2) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_succ
