-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocol_terminal_required
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocol_terminal_required
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:55:44.015474+00:00
-- url     : https://prove2.me/theorems/f504ed74-4a87-4871-9ec8-ccf25dfc7f1d
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol terminal required
-- statement:
--   The terminal physical retry pool requests exactly the prescribed `q`
--   selected blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L291-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Protocol.lean#L291-L295

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocol_terminal_required
    (m w z q : Nat) (hz : 0 < z) :
    decodedRetryPoolBackwardSchedule m w z q
      (decodedRetryPoolProtocolTerminalStage z hz) = q := by sorry
