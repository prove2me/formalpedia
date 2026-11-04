-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverHashes_same_side_independent
-- name    : ThreeSum.TernaryCoverHashes.same_side_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:43:49.877118+00:00
-- url     : https://prove2.me/theorems/c874dddc-766b-43d7-9618-3229f01b7a74
-- title:
--   Ternary Cover Hashes: same side independent
-- statement:
--   The Ternary Cover Hashes construction uses the same side independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L72-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L72-L80

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]

theorem ThreeSum.TernaryCoverHashes.same_side_independent {x y : ι → K} (hxy : x ≠ y) (z : ι → K) :
    LinearIndependent K ![leftVector x, leftVector y, rightVector z] := by sorry
