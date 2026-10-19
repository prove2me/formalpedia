-- Prove2me | Theorems.Thm_PermanentRollout_subtreeCoefficient_branch_right
-- name    : PermanentRollout.subtreeCoefficient_branch_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/b6471a15-9f2b-4eab-b63c-d66bbda043e0
-- title:
--   PermanentRollout.subtreeCoefficient_branch_right
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.subtreeCoefficient_branch_right {ι : Type*} [DecidableEq ι]
    (lam : ℂ) {left right : BlockTree ι}
    (hdisj : Disjoint left.leaves right.leaves) {i : ι}
    (hi : i ∈ right.leaves) :
    subtreeCoefficient lam (.branch left right) i =
      subtreeCoefficientTotal lam left * subtreeCoefficient lam right i := by sorry
