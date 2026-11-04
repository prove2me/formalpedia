-- Prove2me | Theorems.Thm_ThreeSum_LightBandPartition_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandPartition.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:11:18.569796+00:00
-- url     : https://prove2.me/theorems/d68f28ef-43e2-470a-ae9d-8ea158fbd26b
-- title:
--   Light Band Partition: meets
-- statement:
--   The Light Band Partition construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L130-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L130-L177

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandPartition.meets_w3sum_ac885d1 {pMain pDivide pLower pUpper src dst n g d : ℕ}
    (hmain : P[pMain]? = some (body pDivide pLower pUpper))
    (hdiv : P[pDivide]? = some LightSmallDivide.body)
    (hlower : P[pLower]? = some lowerBody) (hupper : P[pUpper]? = some upperBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hspace : dst+2*n ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hd : d+1 ≤ lim.depth) :
    Meets lim P pMain d [src,n,g,dst] μ (time n g)
      (fun r μ' => r = (size n g : ℤ) ∧
        (∀ i < size n g, μ' (dst+i) = f (start g i)) ∧
        (∀ i < size n g, μ' (dst+n+i) = f (stop n g i-1)) ∧
        SameOutside μ μ' dst (2*n)) := by sorry
