-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolInstrumentAux_complete
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:57:11.14342+00:00
-- url     : https://prove2.me/theorems/fefb319f-b135-449e-9334-2a455d135d84
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Instrument Aux complete
-- statement:
--   The physical protocol prefix is complete at every bounded stage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L193-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L193-L212

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) : (stage : Nat) -> (hstage : stage < z) ->
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage hstage).kraus.Complete
  := by sorry
