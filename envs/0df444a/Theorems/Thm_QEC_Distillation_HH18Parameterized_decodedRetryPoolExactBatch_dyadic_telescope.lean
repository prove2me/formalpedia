-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_dyadic_telescope
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_dyadic_telescope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:17:50.502539+00:00
-- url     : https://prove2.me/theorems/75ef3a26-1595-4ef0-9212-7da0cc7dd2cf
-- title:
--   HH18 Parameterized: decoded Retry Pool Exact Batch dyadic telescope
-- statement:
--   A telescoping integer invariant for the accumulated dyadic retry factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L183-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L183-L255

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_dyadic_telescope (z : Nat) :
    3 * 2 ^ z * decodedRetryPoolExactBatchDenominatorProduct z ≤
      (2 ^ (z + 2) - 1) * decodedRetryPoolExactBatchTerminalRequest z := by sorry
