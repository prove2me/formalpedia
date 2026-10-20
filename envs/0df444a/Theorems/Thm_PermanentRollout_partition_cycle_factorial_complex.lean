-- Prove2me | Theorems.Thm_PermanentRollout_partition_cycle_factorial_complex
-- name    : PermanentRollout.partition_cycle_factorial_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/d0e041ff-ee34-4108-865d-10deb9e38df2
-- title:
--   PermanentRollout.partition_cycle_factorial_complex
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.partition_cycle_factorial_complex {t : ℕ}
    (rows : Finset (Fin t)) :
    (∑ partition : Finpartition rows,
      ∏ block ∈ partition.parts,
        ((block.card - 1).factorial : ℂ)) =
      (rows.card.factorial : ℂ) := by sorry
