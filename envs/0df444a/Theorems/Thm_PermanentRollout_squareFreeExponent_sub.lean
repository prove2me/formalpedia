-- Prove2me | Theorems.Thm_PermanentRollout_squareFreeExponent_sub
-- name    : PermanentRollout.squareFreeExponent_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/3e53173a-9960-4404-879d-5a2322c88331
-- title:
--   PermanentRollout.squareFreeExponent_sub
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.squareFreeExponent_sub {ι : Type*} [DecidableEq ι]
    (target removed : Finset ι) :
    squareFreeExponent target - squareFreeExponent removed =
      squareFreeExponent (target \ removed) := by sorry
