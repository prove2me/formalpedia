-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalBucketFilter_meets
-- name    : ThreeSum.LightOriginalBucketFilter.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:57.653427+00:00
-- url     : https://prove2.me/theorems/82266c26-53a6-4022-8f98-e25c84c508df
-- title:
--   Light Original Bucket Filter: meets
-- statement:
--   The Light Original Bucket Filter construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean#L49-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalBucketFilter.lean#L49-L118

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalBucketFilter
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOriginalBucketFilter.meets {pMain keyBase n hist q out d : ℕ} (hmain : P[pMain]? = some body)
    (μ : ℕ → ℤ) (keys counts : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hkeysSpace : keyBase + n ≤ out)
    (hhistSpace : hist + q ≤ out) (hout : out + 2 * n ≤ lim.space) (hkeys : ∀ i < n, keys i < q)
    (hread : ∀ i < n, μ (keyBase + i) = (keys i : ℤ)) (hcounts : ∀ k < q, μ (hist + k) = (counts k : ℤ))
    (hcountWord : ∀ k < q, (counts k : ℤ) ≤ lim.word) (hone : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [keyBase, n, hist, q, out] μ (time n)
      (fun r ν =>
        r = ((bad keys counts n).length : ℤ) ∧
          Seg ν out (cells (good keys counts n)) ∧
            Seg ν (out + n) (cells (bad keys counts n)) ∧ SameOutside μ ν out (2 * n)) := by sorry
