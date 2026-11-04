-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketBuild_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBucketBuild.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:13:24.768764+00:00
-- url     : https://prove2.me/theorems/b5f2c921-7554-48a4-94df-e0c1ee06bfd8
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketBuild.lean#L35-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketBuild.lean#L35-L69

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketBuild
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketBuild.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {keys hist offsets cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hkeys : keys+N ≤ offsets) (hhist : hist+M ≤ offsets)
    (hsep : Apart keys N hist M)
    (hoffsets : offsets+M+1 ≤ cursor) (hcursor : cursor+M ≤ flat)
    (hspace : flat+N ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys+i) = (key i : ℤ)) :
    Meets lim P pMain d [keys,hist,offsets,cursor,flat,N,M] μ (time N M)
      (fun _ ν => Stored ν key N M offsets flat ∧
        (∀ r < M, ν (hist+r) = (count key r N : ℤ)) ∧
        Kept μ ν hist ∧ SameOutside μ ν hist (flat+N-hist)) := by sorry
