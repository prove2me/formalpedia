-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardRootRawCarrier_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardRootRawCarrier_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:09:02.551341+00:00
-- url     : https://prove2.me/theorems/6d91ed9a-6520-429e-97e8-71dea144e0b2
-- title:
--   HH18 Parameterized: decoded Retry Pool Backward Root Raw Carrier card
-- statement:
--   The root raw carrier has the physical input count times the root retry
--   attempt count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L124-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L124-L132

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardRootRawCarrier_card (m w z q : Nat) (hz : 0 < z) :
    Fintype.card (decodedRetryPoolBackwardRootRawCarrier m w z q hz) =
      physicalInputCount m w * decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩ := by sorry
