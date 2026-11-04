-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawACatalog_time_bound
-- name    : ThreeSum.LightBandRawACatalog.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:46.301486+00:00
-- url     : https://prove2.me/theorems/b226a14c-15ce-4e64-a4a7-dbcb3891ed68
-- title:
--   Light Band Raw ACatalog: time bound
-- statement:
--   The Light Band Raw ACatalog construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawACatalog.lean#L165-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawACatalog.lean#L165-L170

import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Theorems.Thm_ThreeSum_LightBandCandidates_time_bound
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Theorems.Thm_ThreeSum_LightBandRawA_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawACatalog
open Light BandEnumeration BandCandidateRows BandRawA
set_option maxHeartbeats 2100000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {tables rec src headerA headerB headerC nA nB nC g vals : ℕ} {f : ℕ → ℤ}

theorem ThreeSum.LightBandRawACatalog.time_bound (a b c g : ℕ) :
    time a b c g ≤ 3000*(LightBandEnumeration.count a b c+a+b+c+1)*(g+1) := by sorry
