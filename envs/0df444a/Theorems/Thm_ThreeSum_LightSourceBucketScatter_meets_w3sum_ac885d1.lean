-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketScatter_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBucketScatter.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:28.680748+00:00
-- url     : https://prove2.me/theorems/56a9dfdc-3ce8-419e-ab99-f43a84073503
-- title:
--   Light Source Bucket Scatter: meets
-- statement:
--   The Light Source Bucket Scatter construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketScatter.lean#L35-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketScatter.lean#L35-L107

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketScatter
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketScatter
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketScatter.meets_w3sum_ac885d1 {pMain : ℕ} (hmain : P[pMain]? = some body)
    {μ : ℕ → ℤ} {keys cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+N ≤ cursor) (hcursor : cursor+M ≤ flat) (hspace : flat+N ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys+i) = (key i : ℤ))
    (hzero : ∀ r < M, μ (cursor+r) = (offset key N r : ℤ)) :
    Meets lim P pMain d [keys,cursor,flat,N,M] μ (time N)
      (fun _ ν => (∀ i < N, ν (flat+position key N i) = (i : ℤ)) ∧
        (∀ r < M, ν (cursor+r) = (offset key N (r+1) : ℤ)) ∧
        SameOutside μ ν cursor (flat+N-cursor)) := by sorry
