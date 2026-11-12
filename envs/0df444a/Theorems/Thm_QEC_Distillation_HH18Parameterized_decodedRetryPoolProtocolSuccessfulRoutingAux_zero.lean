-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingAux_zero
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:57:34.218963+00:00
-- url     : https://prove2.me/theorems/b7a65c0e-3499-4520-bcb4-ffd98586f084
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Successful Routing Aux zero
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Protocol Successful Routing Aux zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L208-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessEvent.lean#L208-L215

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_zero
    (m w z q : Nat) (hz : 0 < z)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q 0 hz) :
    decodedRetryPoolProtocolSuccessfulRoutingAux m w z q 0 hz outcome =
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) outcome := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingAux_zero
