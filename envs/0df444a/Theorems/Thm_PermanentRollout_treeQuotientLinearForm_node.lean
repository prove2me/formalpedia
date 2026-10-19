-- Prove2me | Theorems.Thm_PermanentRollout_treeQuotientLinearForm_node
-- name    : PermanentRollout.treeQuotientLinearForm_node
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/24388d08-ccea-46db-a138-6e927ceb3340
-- title:
--   PermanentRollout.treeQuotientLinearForm_node
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.treeQuotientLinearForm_node {r : ℕ} {ι : Type*}
    [DecidableEq ι] (blocks : ι → Finset (Fin r))
    (left right : BlockTree ι) (ζ : ℂ) (j : ℕ) :
    treeQuotientLinearForm (treeNodeVector blocks left right ζ j) =
      (∑ i ∈ left.leaves, squareZeroBlockSum r (blocks i)) +
        algebraMap ℂ (SquareZeroAlgebra r) (2 * ζ ^ j) *
          (∑ i ∈ right.leaves, squareZeroBlockSum r (blocks i)) := by sorry
