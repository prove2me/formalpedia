-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketSetup_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBucketSetup.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:22:55.940891+00:00
-- url     : https://prove2.me/theorems/7b71c9bd-fe9f-4b09-860f-fcfe74dfb892
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketSetup.lean#L43-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketSetup.lean#L43-L71

import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Theorems.Thm_Light_Ends_next
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketSetup
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketSetup.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {keys N M base : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hM : 0 < M)
    (hkeys : keys+N ≤ base) (hspace : next base N M ≤ lim.space)
    (hkey : ∀ i < N, key i < M) (hread : ∀ i < N, μ (keys+i) = (key i : ℤ)) :
    Meets lim P pMain d [keys,N,M,base] μ (time N M)
      (fun r ν => r = (next base N M : ℤ) ∧
        Stored ν key N M (offsets base M) (flat base M) ∧
        (∀ j < M, ν (hist base+j) = (count key j N : ℤ)) ∧ Kept μ ν base) := by sorry
