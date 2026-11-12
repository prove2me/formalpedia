-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolInstrumentAux_succ
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:56:03.405545+00:00
-- url     : https://prove2.me/theorems/c2a67a45-791c-4d93-86ba-802b640323a9
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Instrument Aux succ
-- statement:
--   One protocol successor is literally the preceding physical prefix bound
--   to the actual nested successor-stage instrument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L161-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L161-L170

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_succ {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z) :
    decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage =
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz stage (by omega)).bind
        (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage) := by sorry
