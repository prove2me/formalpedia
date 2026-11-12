-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulRoutingAux_zero
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:06:32.988407+00:00
-- url     : https://prove2.me/theorems/921ebd0c-b952-4d31-bf85-84ad3f2292df
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successful Routing Aux zero
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Protocol Path Successful Routing Aux zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/SuccessEvent.lean#L50-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/SuccessEvent.lean#L50-L59

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_zero
    (m w z q : Nat) (hz : 0 < z)
    (path : routedDepthOutputSlots m w 0)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q 0 hz) :
    decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q 0 hz path outcome =
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) outcome := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_zero
