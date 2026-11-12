-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_rootInputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_rootInputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:17:08.606867+00:00
-- url     : https://prove2.me/theorems/5d751a34-d7f8-4020-9fd3-0916b2fdb037
-- title:
--   HH18 Parameterized: decoded Retry Pool Exact Batch root Input Slots card
-- statement:
--   The literal physical root carrier for the exact batch has cardinality
--   `n ^ z` times the exact dyadic-denominator product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L157-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L157-L168

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_rootInputSlots_card
    (m w z : Nat) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolRootInputSlots m w (z + 1)
          (decodedRetryPoolExactBatchTerminalRequest (z + 1)) (Nat.succ_pos z)) =
      physicalInputCount m w ^ (z + 1) *
        decodedRetryPoolExactBatchDenominatorProduct (z + 1) := by sorry
