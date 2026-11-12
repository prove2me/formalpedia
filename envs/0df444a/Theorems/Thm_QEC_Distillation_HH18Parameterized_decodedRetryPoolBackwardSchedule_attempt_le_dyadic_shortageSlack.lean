-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardSchedule_attempt_le_dyadic_shortageSlack
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_attempt_le_dyadic_shortageSlack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:08:06.810951+00:00
-- url     : https://prove2.me/theorems/de80e5fd-6807-4a14-9e08-05a89b35b72a
-- title:
--   HH18 Parameterized: decoded Retry Pool Backward Schedule attempt le dyadic shortage Slack
-- statement:
--   Every stage-local retry count obeys the compiled dyadic shortage relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L102-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L102-L110

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_attempt_le_dyadic_shortageSlack
    (m w z q : Nat) (stage : Fin z) :
    decodedRetryPoolBackwardAttempts m w z q stage ≤
      decodedRetryPoolDyadicDenominator stage.1 *
        (decodedRetryPoolBackwardAttempts m w z q stage -
          decodedRetryPoolBackwardSchedule m w z q stage + 1) := by sorry
