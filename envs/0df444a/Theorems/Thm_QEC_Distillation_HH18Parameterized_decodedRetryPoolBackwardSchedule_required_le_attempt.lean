-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardSchedule_required_le_attempt
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_required_le_attempt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:07:31.6192+00:00
-- url     : https://prove2.me/theorems/b5da763b-5c92-459a-9b7d-05e44d479aa3
-- title:
--   HH18 Parameterized: decoded Retry Pool Backward Schedule required le attempt
-- statement:
--   Every stage-local accepted-block request fits into its derived retry
--   attempt count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L93-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L93-L99

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_required_le_attempt
    (m w z q : Nat) (stage : Fin z) :
    decodedRetryPoolBackwardSchedule m w z q stage ≤
      decodedRetryPoolBackwardAttempts m w z q stage := by sorry
