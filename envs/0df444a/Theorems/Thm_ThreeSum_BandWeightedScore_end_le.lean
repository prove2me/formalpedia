-- Prove2me | Theorems.Thm_ThreeSum_BandWeightedScore_end_le
-- name    : ThreeSum.BandWeightedScore.end_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:06.652767+00:00
-- url     : https://prove2.me/theorems/213ccbed-5f69-4bad-ad38-04e3a17f7279
-- title:
--   Band Weighted Score: end le
-- statement:
--   The Band Weighted Score construction uses the end le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L36-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandWeightedScore.lean#L36-L39

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

theorem ThreeSum.BandWeightedScore.end_le {n g a : ℕ} (ha : a*g ≤ n) : a*g+length n g a ≤ n := by sorry
