-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverHashes_left_triple_card
-- name    : ThreeSum.TernaryCoverHashes.left_triple_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:20.718392+00:00
-- url     : https://prove2.me/theorems/c792acf7-1b56-431e-a067-79ec6774db88
-- title:
--   Ternary Cover Hashes: left triple card
-- statement:
--   An additional distinct source on the left contributes one independent
--   hash equation, even when any requested residues coincide.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L139-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L139-L153

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
variable [Fintype K] [DecidableEq K] [DecidableEq ι]

theorem ThreeSum.TernaryCoverHashes.left_triple_card {x u : ι → K} (hxu : x ≠ u) (y : ι → K) (a b c : K) :
    Fintype.card K ^ 3 *
      ((pairEvent x y a b).filter fun w => linearHash (leftVector u) w = c).card =
        Fintype.card (Coordinate ι → K) := by sorry
