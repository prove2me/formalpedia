-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRootInputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRootInputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:08:53.2396+00:00
-- url     : https://prove2.me/theorems/4d528ad7-6732-4a8c-90f5-c86bbed2b5ad
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Root Input Slots card
-- statement:
--   The actual root carrier has one physical block for every derived root
--   retry attempt.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L43-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L43-L48

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRootInputSlots_card
    (m w z q : Nat) (hz : 0 < z) :
    Fintype.card (decodedRetryPoolPhysicalProtocolRootInputSlots m w z q hz) =
      physicalInputCount m w *
        decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ := by sorry
