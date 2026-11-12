-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardTerminalGoodCarrier_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardTerminalGoodCarrier_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:08:45.511606+00:00
-- url     : https://prove2.me/theorems/1821b62c-d2ed-47f5-b953-4d0d0e8b5679
-- title:
--   HH18 Parameterized: decoded Retry Pool Backward Terminal Good Carrier card
-- statement:
--   The terminal good carrier has the requested number of outputs times the
--   logical output count raised to the exact finite depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L136-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L136-L139

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardTerminalGoodCarrier_card (m w z q : Nat) :
    Fintype.card (decodedRetryPoolBackwardTerminalGoodCarrier m w z q) =
      q * logicalOutputCount m w ^ z := by sorry
