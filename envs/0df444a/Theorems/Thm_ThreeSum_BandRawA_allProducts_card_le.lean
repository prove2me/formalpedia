-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_allProducts_card_le
-- name    : ThreeSum.BandRawA.allProducts_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:40.045837+00:00
-- url     : https://prove2.me/theorems/249a060e-99ee-4df8-9788-8e0d72d09420
-- title:
--   Band Raw A: all Products card le
-- statement:
--   The Band Raw A construction uses the all Products card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L94-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAScore.lean#L94-L102

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.allProducts_card_le (nA nB nC g : ℕ) (rs : List Record) :
    (allProducts nA nB nC g rs).card ≤ rs.length*g^3 := by sorry
