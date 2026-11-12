-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatchDenominatorProduct_pos
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatchDenominatorProduct_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:07:25.550054+00:00
-- url     : https://prove2.me/theorems/c1d90394-3b7f-494d-ad94-d48ca63ddc50
-- title:
--   HH18 Parameterized: decoded Retry Pool Exact Batch Denominator Product pos
-- statement:
--   The exact dyadic-denominator product is always positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L267-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L267-L273

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatchDenominatorProduct_pos (z : Nat) :
    0 < decodedRetryPoolExactBatchDenominatorProduct z := by sorry
