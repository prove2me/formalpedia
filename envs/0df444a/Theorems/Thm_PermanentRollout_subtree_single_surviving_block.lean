-- Prove2me | Theorems.Thm_PermanentRollout_subtree_single_surviving_block
-- name    : PermanentRollout.subtree_single_surviving_block
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/57380e4e-438a-4371-a5e0-4524bb0e30f0
-- title:
--   PermanentRollout.subtree_single_surviving_block
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.subtree_single_surviving_block
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (y : ι → R) (t d : ℕ) {i : ι}
    (hi : i ∈ s) (hd : d ≤ t)
    (hnil : ∀ j ∈ s, y j ^ (t + 1) = 0) :
    (y i ^ (t - d) * ∏ j ∈ s.erase i, y j ^ t) *
        (∑ j ∈ s, y j) ^ d =
      ∏ j ∈ s, y j ^ t := by sorry
