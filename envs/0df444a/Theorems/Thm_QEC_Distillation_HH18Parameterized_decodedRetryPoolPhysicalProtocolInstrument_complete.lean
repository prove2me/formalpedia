-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolInstrument_complete
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolInstrument_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:54:57.091311+00:00
-- url     : https://prove2.me/theorems/f090afc8-9f75-494a-831f-504b8f6668f6
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Instrument complete
-- statement:
--   The full physical protocol finite instrument is complete.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L269-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L269-L275

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) :
    (decodedRetryPoolPhysicalProtocolInstrument
      h hdegree z q hz).kraus.Complete := by sorry
