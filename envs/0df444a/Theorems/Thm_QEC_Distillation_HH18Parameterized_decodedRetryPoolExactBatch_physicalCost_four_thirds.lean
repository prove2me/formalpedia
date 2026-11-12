-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_physicalCost_four_thirds
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_physicalCost_four_thirds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:18:57.1963+00:00
-- url     : https://prove2.me/theorems/e1937832-6fb1-4da6-aed4-1674658d80c8
-- title:
--   HH18 Parameterized: decoded Retry Pool Exact Batch physical Cost four thirds
-- statement:
--   For the exact divisible terminal batch, the literal physical root carrier
--   has at most a `4/3` retry factor over the `n^z/k^z` input/output ratio.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L298-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/ExactBatching.lean#L298-L313

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_physicalCost_four_thirds
    (m w z : Nat) :
    3 * logicalOutputCount m w ^ (z + 1) *
        Fintype.card
          (decodedRetryPoolPhysicalProtocolRootInputSlots m w (z + 1)
            (decodedRetryPoolExactBatchTerminalRequest (z + 1)) (Nat.succ_pos z)) ≤
      4 * physicalInputCount m w ^ (z + 1) *
        Fintype.card
          (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w (z + 1)
            (decodedRetryPoolExactBatchTerminalRequest (z + 1))) := by sorry
