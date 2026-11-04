-- Prove2me | Theorems.Thm_ThreeSum_LightRadixRows_meets_w3sum_ac885d1
-- name    : ThreeSum.LightRadixRows.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:30.125316+00:00
-- url     : https://prove2.me/theorems/8418737f-c406-48b1-8f6c-d76e289cb55e
-- title:
--   Light Radix Rows: meets
-- statement:
--   The Light Radix Rows construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean#L36-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean#L36-L119

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Theorems.Thm_ThreeSum_LightReportingAffine_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixRows
open Light RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRadixRows.meets_w3sum_ac885d1 {pMain pAffine srcBase srcPrev dst p U V : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pAffine))
    (haffine : P[pAffine]? = some LightReportingAffine.body)
    (base prev : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hbaseEnd : srcBase+base.length ≤ dst) (hprevEnd : srcPrev+prev.length ≤ dst)
    (hspace : dst+base.length*prev.length ≤ lim.space)
    (hword : (word p U V : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hbaseRead : Seg μ srcBase base) (hprevRead : Seg μ srcPrev prev)
    (hbaseBound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hprevBound : ∀ y ∈ prev, |y| ≤ (V : ℤ)) :
    Meets lim P pMain d [srcBase,srcPrev,dst,base.length,prev.length,p] μ
      (time base.length prev.length)
      (fun _ ν => Seg ν dst (step (p : ℤ) base prev) ∧
        SameOutside μ ν dst (base.length*prev.length)) := by sorry
