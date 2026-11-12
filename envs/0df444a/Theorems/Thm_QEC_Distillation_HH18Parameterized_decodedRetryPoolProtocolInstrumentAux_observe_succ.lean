-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolInstrumentAux_observe_succ
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_observe_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:40:56.990447+00:00
-- url     : https://prove2.me/theorems/2e54f7d9-792a-43cb-a6d2-1835a69919b8
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Instrument Aux observe succ
-- statement:
--   A successor observation retains the entire previous history and appends
--   the actual nested successor-stage observation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L174-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L174-L190

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_observe_succ {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (firstIndex : decodedRetryPoolProtocolRawIndexAux
      h hdegree z q stage (by omega))
    (secondIndex : nestedTensorHistory
      (decodedRetryPoolSuccessorStageRawIndex
        h hdegree z q ⟨stage, by omega⟩ hstage)
      (logicalOutputCount m w) stage) :
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz (stage + 1) hstage).observe
        (firstIndex, secondIndex) =
      ⟨(decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage (by omega)).observe firstIndex,
        (decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage).observe secondIndex⟩ := by sorry
