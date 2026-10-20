-- Prove2me | Theorems.Thm_PermanentRollout_squareFreeExponent_sum
-- name    : PermanentRollout.squareFreeExponent_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/fb3bbb72-b6a0-4c92-a09a-94a5db19650c
-- title:
--   PermanentRollout.squareFreeExponent_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.squareFreeExponent_sum {ι : Type*} (rows : Finset ι) :
    (squareFreeExponent rows).sum (fun _ n => n) = rows.card := by sorry
