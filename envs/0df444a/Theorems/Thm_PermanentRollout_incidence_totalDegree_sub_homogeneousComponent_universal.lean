-- Prove2me | Theorems.Thm_PermanentRollout_incidence_totalDegree_sub_homogeneousComponent_universal
-- name    : PermanentRollout.incidence_totalDegree_sub_homogeneousComponent_universal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/843a2dd6-87bc-4e77-a041-300a4edbb584
-- title:
--   PermanentRollout.incidence_totalDegree_sub_homogeneousComponent_universal
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.incidence_totalDegree_sub_homogeneousComponent_universal
    {σ B : Type*} [CommRing B]
    (f : MvPolynomial σ B) {q : ℕ}
    (hf : f.totalDegree ≤ q) :
    (f - MvPolynomial.homogeneousComponent q f).totalDegree ≤ q - 1 := by sorry
