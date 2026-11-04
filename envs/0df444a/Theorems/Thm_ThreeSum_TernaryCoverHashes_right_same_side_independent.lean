-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverHashes_right_same_side_independent
-- name    : ThreeSum.TernaryCoverHashes.right_same_side_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:06.571448+00:00
-- url     : https://prove2.me/theorems/962484f6-9223-40f9-b00b-e3f51c7bec88
-- title:
--   Ternary Cover Hashes: right same side independent
-- statement:
--   The Ternary Cover Hashes construction uses the right same side independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L101-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L101-L109

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]

theorem ThreeSum.TernaryCoverHashes.right_same_side_independent {x y : ι → K} (hxy : x ≠ y) (z : ι → K) :
    LinearIndependent K ![rightVector x, rightVector y, leftVector z] := by sorry
