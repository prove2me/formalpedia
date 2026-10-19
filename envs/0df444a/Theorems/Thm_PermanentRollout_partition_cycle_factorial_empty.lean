-- Prove2me | Theorems.Thm_PermanentRollout_partition_cycle_factorial_empty
-- name    : PermanentRollout.partition_cycle_factorial_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/6efcea80-65b1-433e-99a7-95875d1cabc7
-- title:
--   PermanentRollout.partition_cycle_factorial_empty
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.partition_cycle_factorial_empty (t : ℕ) :
    (∑ partition : Finpartition (∅ : Finset (Fin t)),
      ∏ block ∈ partition.parts, (block.card - 1).factorial) =
        (0 : ℕ).factorial := by sorry
