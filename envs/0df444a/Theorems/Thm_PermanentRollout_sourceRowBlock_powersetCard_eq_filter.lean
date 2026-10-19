-- Prove2me | Theorems.Thm_PermanentRollout_sourceRowBlock_powersetCard_eq_filter
-- name    : PermanentRollout.sourceRowBlock_powersetCard_eq_filter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/569a1ad2-cead-43f1-bf62-f18cf4d1f94f
-- title:
--   PermanentRollout.sourceRowBlock_powersetCard_eq_filter
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceRowBlock_powersetCard_eq_filter
    (b t d : ℕ) (h : Fin b) :
    (sourceRowBlock b t h).powersetCard d =
      ((Finset.univ : Finset (Fin (b * t))).powersetCard d).filter
        (fun omitted => omitted ⊆ sourceRowBlock b t h) := by sorry
