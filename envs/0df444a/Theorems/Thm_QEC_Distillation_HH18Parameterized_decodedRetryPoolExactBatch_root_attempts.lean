-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_root_attempts
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_root_attempts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:17:59.993865+00:00
-- url     : https://prove2.me/theorems/8dd62e64-3936-4091-aabf-ba4d6332dc36
-- title:
--   HH18 Parameterized: decoded Retry Pool Exact Batch root attempts
-- statement:
--   At positive depth, an exact terminal batch makes the root attempt count
--   equal to the base physical growth times the product of dyadic denominators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L112-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L112-L153

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_root_attempts
    (m w z multiple : Nat) :
    decodedRetryPoolBackwardAttempts m w (z + 1)
        (multiple * decodedRetryPoolExactBatchTerminalRequest (z + 1))
        ⟨0, Nat.succ_pos z⟩ =
      multiple * physicalInputCount m w ^ z *
        decodedRetryPoolExactBatchDenominatorProduct (z + 1) := by sorry
