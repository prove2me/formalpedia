-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_terminalOutputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_terminalOutputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:11:44.913091+00:00
-- url     : https://prove2.me/theorems/3cc07316-0b4a-4ae7-a288-a24f41911453
-- title:
--   HH18 Parameterized: decoded Retry Pool Exact Batch terminal Output Slots card
-- statement:
--   The literal terminal carrier for the exact batch has cardinality equal to
--   the terminal batch factor times `k ^ z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L172-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L172-L180

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_terminalOutputSlots_card
    (m w z : Nat) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w z
          (decodedRetryPoolExactBatchTerminalRequest z)) =
      decodedRetryPoolExactBatchTerminalRequest z *
        logicalOutputCount m w ^ z := by sorry
