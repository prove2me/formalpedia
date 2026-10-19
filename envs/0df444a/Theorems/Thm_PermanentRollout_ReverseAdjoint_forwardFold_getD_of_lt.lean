-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_forwardFold_getD_of_lt
-- name    : PermanentRollout.ReverseAdjoint.forwardFold_getD_of_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/391f81ed-7791-4174-98a8-af52dc9bdb41
-- title:
--   PermanentRollout.ReverseAdjoint.forwardFold_getD_of_lt
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint

theorem PermanentRollout.ReverseAdjoint.forwardFold_getD_of_lt {ι : Type*}
    (program : List (FreeAffineInstruction ι))
    (values : Array (MvPolynomial ι ℂ))
    (index : ℕ) (hindex : index < values.size) :
    (program.foldl forwardStep values).getD index 0 =
      values.getD index 0 := by sorry
