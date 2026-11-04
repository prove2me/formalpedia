-- Prove2me | Theorems.Thm_ThreeSum_LightBandPartition_lower_meets
-- name    : ThreeSum.LightBandPartition.lower_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:15.573957+00:00
-- url     : https://prove2.me/theorems/ba72fca2-6ccc-4e44-80d1-521cf2fcbe0d
-- title:
--   Light Band Partition: lower meets
-- statement:
--   The Light Band Partition construction uses the lower meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L25-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L25-L46

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandPartition.lower_meets {p src dst n g d : ℕ} (hp : P[p]? = some lowerBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hdst : dst+size n g ≤ lim.space)
    (hread : ∀ i < n, μ (src+i) = f i) :
    Meets lim P p d [src,dst,size n g,g] μ (lowerTime (size n g))
      (fun _ μ' => (∀ i < size n g, μ' (dst+i) = f (start g i)) ∧
        SameOutside μ μ' dst (size n g)) := by sorry
