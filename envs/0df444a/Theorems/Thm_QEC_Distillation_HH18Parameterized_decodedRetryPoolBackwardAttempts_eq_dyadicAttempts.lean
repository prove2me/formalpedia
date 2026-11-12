-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardAttempts_eq_dyadicAttempts
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardAttempts_eq_dyadicAttempts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:07:00.507092+00:00
-- url     : https://prove2.me/theorems/317752bd-9b39-4904-9018-cbebc541a661
-- title:
--   HH18 Parameterized: decoded Retry Pool Backward Attempts eq dyadic Attempts
-- statement:
--   The forward-stage retry attempt is exactly the compiled dyadic attempt
--   count for that stage's required accepted blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L85-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L85-L89

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardAttempts_eq_dyadicAttempts
    (m w z q : Nat) (stage : Fin z) :
    decodedRetryPoolBackwardAttempts m w z q stage =
      decodedRetryPoolDyadicAttempts stage.1
        (decodedRetryPoolBackwardSchedule m w z q stage) := by sorry
