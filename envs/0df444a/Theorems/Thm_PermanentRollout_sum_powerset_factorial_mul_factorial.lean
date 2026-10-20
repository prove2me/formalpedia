-- Prove2me | Theorems.Thm_PermanentRollout_sum_powerset_factorial_mul_factorial
-- name    : PermanentRollout.sum_powerset_factorial_mul_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/257900ae-1dea-4df9-a29b-f5546508e9b0
-- title:
--   PermanentRollout.sum_powerset_factorial_mul_factorial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sum_powerset_factorial_mul_factorial {α : Type*}
    [DecidableEq α] (rows : Finset α) :
    (∑ selected ∈ rows.powerset,
      selected.card.factorial * (rows \ selected).card.factorial) =
        (rows.card + 1).factorial := by sorry
