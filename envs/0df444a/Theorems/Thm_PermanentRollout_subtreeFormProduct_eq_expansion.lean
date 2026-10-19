-- Prove2me | Theorems.Thm_PermanentRollout_subtreeFormProduct_eq_expansion
-- name    : PermanentRollout.subtreeFormProduct_eq_expansion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/e015325b-2c88-4a12-8f1e-ed41a675ea68
-- title:
--   PermanentRollout.subtreeFormProduct_eq_expansion
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.subtreeFormProduct_eq_expansion
    {R ι : Type*} [CommSemiring R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (hd : d ≤ t) (lam : ℂ)
    (tree : BlockTree ι) (hnodup : tree.leafList.Nodup)
    (hnil : ∀ i ∈ tree.leaves, y i ^ (t + 1) = 0) :
    subtreeFormProduct y t d lam tree =
      ∑ i ∈ tree.leaves,
        algebraMap ℂ R (subtreeCoefficient lam tree i) *
          (y i ^ (t - d) * ∏ j ∈ tree.leaves.erase i, y j ^ t) := by sorry
