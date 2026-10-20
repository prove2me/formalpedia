-- Prove2me | Theorems.Thm_PermanentRollout_subtreeLinearFormProduct_eq_expansion
-- name    : PermanentRollout.subtreeLinearFormProduct_eq_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/c7f830ef-fe8c-4e27-b841-8a3b8a401b25
-- title:
--   PermanentRollout.subtreeLinearFormProduct_eq_expansion
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.subtreeLinearFormProduct_eq_expansion
    {R ι : Type*} [CommRing R] [Algebra ℂ R] [DecidableEq ι]
    (y : ι → R) (t d : ℕ) (hdpos : 0 < d) (hd : d ≤ t)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (tree : BlockTree ι) (hnodup : tree.leafList.Nodup)
    (hnil : ∀ i ∈ tree.leaves, y i ^ (t + 1) = 0) :
    subtreeLinearFormProduct y t d ζ tree =
      ∑ i ∈ tree.leaves,
        algebraMap ℂ R
            (subtreeCoefficient
              (((-1 : ℂ) ^ (d + 1)) * (2 : ℂ) ^ d) tree i) *
          (y i ^ (t - d) * ∏ j ∈ tree.leaves.erase i, y j ^ t) := by sorry
