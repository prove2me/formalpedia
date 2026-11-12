-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchInputOutputRatio_le_four_thirds
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchInputOutputRatio_le_four_thirds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:07:12.246798+00:00
-- url     : https://prove2.me/theorems/9ad5e8c4-dc83-4c55-956c-41bb61b12b26
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Input Output Ratio le four thirds
-- statement:
--   The actual exact-batch input/output slot ratio has only the uniform
--   `4/3` retry overhead beyond `(n/k)^(depth+1)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L99-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L99-L152

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchInputOutputRatio_le_four_thirds
    (m w depth : Nat) :
    DependentBatch.typedInputOutputRatio
        (decodedRetryPoolPhysicalExactBatchInputSlots m w depth)
        (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) <=
      (4 / 3 : Real) *
        ((physicalInputCount m w : Real) / logicalOutputCount m w) ^
          (depth + 1) := by sorry
