-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardSchedule_preterminal
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_preterminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:04:49.297195+00:00
-- url     : https://prove2.me/theorems/b374d649-a494-4128-9e53-98824282ed97
-- title:
--   HH18 Parameterized: decoded Retry Pool Backward Schedule preterminal
-- statement:
--   At depth two, the root demand is the physical input count times the
--   derived retry attempts of the terminal request.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L75-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L75-L81

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_preterminal (m w z q : Nat) (hdepth : z = 2) :
    decodedRetryPoolBackwardSchedule m w z q ⟨0, by omega⟩ =
      physicalInputCount m w * decodedRetryPoolDyadicAttempts 1 q := by sorry
