-- Prove2me | Theorems.Thm_ThreeSum_BandWeightedScore_position_lt
-- name    : ThreeSum.BandWeightedScore.position_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:08.519663+00:00
-- url     : https://prove2.me/theorems/2ebce6bf-9801-4468-bdc0-be406831e8d5
-- title:
--   Band Weighted Score: position lt
-- statement:
--   The Band Weighted Score construction uses the position lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L31-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L31-L34

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

theorem ThreeSum.BandWeightedScore.position_lt {n g a i : ℕ} (hi : i < length n g a) : a*g+i < n := by sorry
