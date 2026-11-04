-- Prove2me | Theorems.Thm_ThreeSum_BandWeightedScore_length_eq_partition
-- name    : ThreeSum.BandWeightedScore.length_eq_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:00.535329+00:00
-- url     : https://prove2.me/theorems/e031db9f-12a4-4366-a985-b0db4598f088
-- title:
--   Band Weighted Score: length eq partition
-- statement:
--   The Band Weighted Score construction uses the length eq partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L25-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L25-L29

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

theorem ThreeSum.BandWeightedScore.length_eq_partition (n g a : ℕ) :
    length n g a=BandPartition.stop n g a-BandPartition.start g a := by sorry
