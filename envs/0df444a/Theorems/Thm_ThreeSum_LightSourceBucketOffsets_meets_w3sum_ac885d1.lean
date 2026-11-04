-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketOffsets_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBucketOffsets.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:32.998012+00:00
-- url     : https://prove2.me/theorems/3e7c1ad1-2620-49ea-97e0-5a754b2e1cb7
-- title:
--   Light Source Bucket Offsets: meets
-- statement:
--   The Light Source Bucket Offsets construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketOffsets.lean#L36-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketOffsets.lean#L36-L113

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOffsets
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketOffsets
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketOffsets.meets_w3sum_ac885d1 {pMain : ℕ} (hmain : P[pMain]? = some body)
    {μ : ℕ → ℤ} {hist offsets cursor M N : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hN : (N : ℤ) ≤ lim.word)
    (hhist : hist+M ≤ offsets) (hoffsets : offsets+M+1 ≤ cursor)
    (hspace : cursor+M ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ r < M, μ (hist+r) = (count key r N : ℤ)) :
    Meets lim P pMain d [hist,offsets,cursor,M,N] μ (time M)
      (fun _ ν => (∀ r ≤ M, ν (offsets+r) = (offset key N r : ℤ)) ∧
        (∀ r < M, ν (cursor+r) = (offset key N r : ℤ)) ∧
        SameOutside μ ν offsets (cursor+M-offsets)) := by sorry
