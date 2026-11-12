-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_backwardRequired_succ
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_backwardRequired_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:18:56.783376+00:00
-- url     : https://prove2.me/theorems/cff1de67-2b30-4243-8a58-fd5e59bfe243
-- title:
--   HH18 Parameterized: decoded Retry Pool Exact Batch backward Required succ
-- statement:
--   Removing the highest exact batching factor turns a successor-depth
--   backward schedule into the preceding-depth schedule with its physical and
--   dyadic multipliers carried into the terminal request.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L76-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L76-L108

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_backwardRequired_succ
    (m w z multiple distance : Nat) :
    decodedRetryPoolBackwardRequiredAtDistance m w (z + 1)
        (multiple * decodedRetryPoolExactBatchTerminalRequest (z + 1))
        (distance + 1) =
      decodedRetryPoolBackwardRequiredAtDistance m w z
        ((physicalInputCount m w * decodedRetryPoolDyadicDenominator z * multiple) *
          decodedRetryPoolExactBatchTerminalRequest z)
        distance := by sorry
