-- Prove2me | Theorems.Thm_PermanentRollout_rootOfUnity_subtreeCoefficient_and_total_ne_zero
-- name    : PermanentRollout.rootOfUnity_subtreeCoefficient_and_total_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/93b5a565-eec9-43eb-8d0b-408b071d2555
-- title:
--   PermanentRollout.rootOfUnity_subtreeCoefficient_and_total_ne_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.rootOfUnity_subtreeCoefficient_and_total_ne_zero
    {ι : Type*} [DecidableEq ι] {d : ℕ} (hd : 0 < d)
    (tree : BlockTree ι) (hnodup : tree.leafList.Nodup) :
    let lam : ℂ := (-1 : ℂ) ^ (d + 1) * (2 : ℂ) ^ d
    (∀ i ∈ tree.leaves, subtreeCoefficient lam tree i ≠ 0) ∧
      subtreeCoefficientTotal lam tree ≠ 0 := by sorry
