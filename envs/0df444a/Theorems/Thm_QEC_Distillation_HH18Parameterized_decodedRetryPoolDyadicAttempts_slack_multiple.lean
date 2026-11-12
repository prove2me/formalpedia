-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolDyadicAttempts_slack_multiple
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicAttempts_slack_multiple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:11:41.382641+00:00
-- url     : https://prove2.me/theorems/d94d9e38-7681-4f08-8b9a-985e981d9538
-- title:
--   HH18 Parameterized: decoded Retry Pool Dyadic Attempts slack multiple
-- statement:
--   A request divisible by the stage slack makes the compiled ceiling exact.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L43-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L43-L71

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolDyadicAttempts_slack_multiple
    (stage multiple : Nat) :
    decodedRetryPoolDyadicAttempts stage
        ((decodedRetryPoolDyadicDenominator stage - 1) * multiple) =
      decodedRetryPoolDyadicDenominator stage * multiple := by sorry
