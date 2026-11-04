-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBucketFromHistogram.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:46.056588+00:00
-- url     : https://prove2.me/theorems/139b732b-9229-40b8-b355-29720c5f3c63
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketFromHistogram.lean#L37-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketFromHistogram.lean#L37-L72

import Definitions.Def_Submission_ThreeSum_LightSourceBucketOffsets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketScatter
import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketFromHistogram
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketFromHistogram.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {keys hist offsets cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hkeys : keys+N ≤ offsets) (hhist : hist+M ≤ offsets)
    (hoffsets : offsets+M+1 ≤ cursor) (hcursor : cursor+M ≤ flat)
    (hspace : flat+N ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys+i) = (key i : ℤ))
    (hhistRead : ∀ r < M, μ (hist+r) = (count key r N : ℤ)) :
    Meets lim P pMain d [keys,hist,offsets,cursor,flat,N,M] μ (time N M)
      (fun _ ν => Stored ν key N M offsets flat ∧ Kept μ ν offsets ∧
        SameOutside μ ν offsets (flat+N-offsets)) := by sorry
