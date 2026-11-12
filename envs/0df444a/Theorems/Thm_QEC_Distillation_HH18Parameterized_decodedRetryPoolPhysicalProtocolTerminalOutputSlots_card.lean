-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolTerminalOutputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolTerminalOutputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:16:48.471206+00:00
-- url     : https://prove2.me/theorems/183a5724-e91f-4275-935f-2f25caa49139
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Terminal Output Slots card
-- statement:
--   The actual terminal carrier has the requested batch factor times exactly
--   `k ^ z` logical output slots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L52-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L52-L56

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolTerminalOutputSlots_card
    (m w z q : Nat) :
    Fintype.card (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w z q) =
      q * logicalOutputCount m w ^ z := by sorry
