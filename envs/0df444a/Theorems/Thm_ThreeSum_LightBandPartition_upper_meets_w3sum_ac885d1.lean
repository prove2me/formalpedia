-- Prove2me | Theorems.Thm_ThreeSum_LightBandPartition_upper_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandPartition.upper_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:19.424887+00:00
-- url     : https://prove2.me/theorems/18234b86-2d23-4c34-aaeb-1c997323c634
-- title:
--   Light Band Partition: upper meets
-- statement:
--   The Light Band Partition construction uses the upper meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L56-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L56-L115

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandPartition.upper_meets_w3sum_ac885d1 {p src dst n g d : ℕ} (hp : P[p]? = some upperBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hdst : dst+size n g ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) :
    Meets lim P p d [src,n,g,dst,size n g] μ (upperTime (size n g))
      (fun _ μ' => (∀ i < size n g, μ' (dst+i) = f (stop n g i-1)) ∧
        SameOutside μ μ' dst (size n g)) := by sorry
