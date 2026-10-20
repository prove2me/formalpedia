-- Prove2me | Theorems.Thm_PermanentRollout_powersetCard_erase_eq_filter_not_mem
-- name    : PermanentRollout.powersetCard_erase_eq_filter_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/88a9f854-eb9c-431b-b42d-d5595fdc114b
-- title:
--   PermanentRollout.powersetCard_erase_eq_filter_not_mem
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.powersetCard_erase_eq_filter_not_mem {α : Type*} [DecidableEq α]
    (s : Finset α) (i : α) (q : ℕ) :
    (s.erase i).powersetCard q =
      (s.powersetCard q).filter (fun rows => i ∉ rows) := by sorry
