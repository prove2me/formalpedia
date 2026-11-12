-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchOutputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchOutputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:06:40.23344+00:00
-- url     : https://prove2.me/theorems/ff0ccc4b-6924-458b-a25f-5b6bc136ec79
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Output Slots card
-- statement:
--   The literal output-coordinate carrier has the exact batch factor times
--   `k^(depth+1)` terminal qubits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L88-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L88-L95

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchOutputSlots_card
    (m w depth : Nat) :
    Fintype.card (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) =
      decodedRetryPoolExactBatchTerminalRequest (depth + 1) *
        logicalOutputCount m w ^ (depth + 1) := by sorry
