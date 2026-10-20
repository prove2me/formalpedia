-- Prove2me | Theorems.Thm_PermanentRollout_sourceRowBlock_exceptional_unique
-- name    : PermanentRollout.sourceRowBlock_exceptional_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/99d616df-b9b0-442f-9c0f-6b94dc0c57bc
-- title:
--   PermanentRollout.sourceRowBlock_exceptional_unique
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceRowBlock_exceptional_unique
    {b t : ℕ} (omitted : Finset (Fin (b * t)))
    (hnonempty : omitted.Nonempty) {left right : Fin b}
    (hleft : omitted ⊆ sourceRowBlock b t left)
    (hright : omitted ⊆ sourceRowBlock b t right) :
    left = right := by sorry
