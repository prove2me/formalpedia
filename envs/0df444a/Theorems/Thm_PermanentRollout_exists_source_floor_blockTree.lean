-- Prove2me | Theorems.Thm_PermanentRollout_exists_source_floor_blockTree
-- name    : PermanentRollout.exists_source_floor_blockTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/4d5df9b3-19b6-43cf-b9e9-067aa9762975
-- title:
--   PermanentRollout.exists_source_floor_blockTree
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

theorem PermanentRollout.exists_source_floor_blockTree
    {n d : ℕ} (hd : 3 ≤ d) (hn : 6 * blockWidth d ≤ n) :
    ∃ tree : BlockTree (Fin (blockCount n d)),
      tree.leafList.Nodup ∧ tree.leaves = Finset.univ := by sorry
