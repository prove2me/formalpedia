-- Prove2me | Theorems.Thm_PermanentRollout_subtreeTopProduct_mul_other_sum_eq_zero
-- name    : PermanentRollout.subtreeTopProduct_mul_other_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/03429fef-fe8f-4634-af83-1c90a777a406
-- title:
--   PermanentRollout.subtreeTopProduct_mul_other_sum_eq_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.subtreeTopProduct_mul_other_sum_eq_zero
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (y : ι → R) (t : ℕ) (i : ι)
    (hnil : ∀ j ∈ s, y j ^ (t + 1) = 0) :
    (∏ j ∈ s.erase i, y j ^ t) *
        (∑ j ∈ s.erase i, y j) = 0 := by sorry
