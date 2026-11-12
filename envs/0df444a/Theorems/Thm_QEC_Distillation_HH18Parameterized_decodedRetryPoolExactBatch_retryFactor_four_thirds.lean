-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_retryFactor_four_thirds
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_retryFactor_four_thirds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:18:37.248792+00:00
-- url     : https://prove2.me/theorems/1260a731-517c-4c1e-ac9d-074a39b30854
-- title:
--   HH18 Parameterized: decoded Retry Pool Exact Batch retry Factor four thirds
-- statement:
--   The accumulated exact retry multiplier is uniformly at most `4/3` in
--   cross-multiplied natural-number form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L277-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L277-L294

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_retryFactor_four_thirds (z : Nat) :
    3 * decodedRetryPoolExactBatchDenominatorProduct z ≤
      4 * decodedRetryPoolExactBatchTerminalRequest z := by sorry
