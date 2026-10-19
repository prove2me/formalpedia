-- Prove2me | Theorems.Thm_PermanentRollout_subtree_topProduct_union_erase_left
-- name    : PermanentRollout.subtree_topProduct_union_erase_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/e393cfb2-11aa-4937-b81d-e740c5e402fb
-- title:
--   PermanentRollout.subtree_topProduct_union_erase_left
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.subtree_topProduct_union_erase_left
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (left right : Finset ι) (hdisj : Disjoint left right)
    (y : ι → R) (t : ℕ) {i : ι} (hi : i ∈ left) :
    (∏ j ∈ (left ∪ right).erase i, y j ^ t) =
      (∏ j ∈ left.erase i, y j ^ t) *
        ∏ j ∈ right, y j ^ t := by sorry
