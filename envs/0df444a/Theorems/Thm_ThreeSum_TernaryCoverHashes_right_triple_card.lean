-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverHashes_right_triple_card
-- name    : ThreeSum.TernaryCoverHashes.right_triple_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:22.024811+00:00
-- url     : https://prove2.me/theorems/851467ec-5954-4875-86f1-0471fffeba1c
-- title:
--   Ternary Cover Hashes: right triple card
-- statement:
--   The Ternary Cover Hashes construction uses the right triple card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L155-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L155-L169

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
variable [Fintype K] [DecidableEq K] [DecidableEq ι]

theorem ThreeSum.TernaryCoverHashes.right_triple_card (x : ι → K) {y v : ι → K} (hyv : y ≠ v) (a b c : K) :
    Fintype.card K ^ 3 *
      ((pairEvent x y a b).filter fun w => linearHash (rightVector v) w = c).card =
        Fintype.card (Coordinate ι → K) := by sorry
