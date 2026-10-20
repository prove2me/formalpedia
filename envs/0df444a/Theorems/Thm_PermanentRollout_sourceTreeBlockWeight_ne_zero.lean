-- Prove2me | Theorems.Thm_PermanentRollout_sourceTreeBlockWeight_ne_zero
-- name    : PermanentRollout.sourceTreeBlockWeight_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/68687bd7-a7cc-47b3-b849-d2d42d47da7c
-- title:
--   PermanentRollout.sourceTreeBlockWeight_ne_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.sourceTreeBlockWeight_ne_zero
    {b d : ℕ} (hd : 0 < d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    ∀ h : Fin b, sourceTreeBlockWeight b d tree h ≠ 0 := by sorry
