-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverHashes_pairEvent_card
-- name    : ThreeSum.TernaryCoverHashes.pairEvent_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:13:31.381888+00:00
-- url     : https://prove2.me/theorems/9bef852d-26e7-49bc-a9cf-84185f9c184c
-- title:
--   Ternary Cover Hashes: pair Event card
-- statement:
--   Exactly uniform counts for the actual tagged pair, with no inequality
--   between requested residues or untagged endpoint words.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L124-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L124-L135

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_card

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
variable [Fintype K] [DecidableEq K] [DecidableEq ι]

theorem ThreeSum.TernaryCoverHashes.pairEvent_card (x y : ι → K) (a b : K) :
    Fintype.card K ^ 2 * (pairEvent x y a b).card =
      Fintype.card (Coordinate ι → K) := by sorry
