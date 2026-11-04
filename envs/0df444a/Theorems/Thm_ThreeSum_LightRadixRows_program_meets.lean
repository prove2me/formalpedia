-- Prove2me | Theorems.Thm_ThreeSum_LightRadixRows_program_meets
-- name    : ThreeSum.LightRadixRows.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:37:28.453971+00:00
-- url     : https://prove2.me/theorems/b7c5faed-9636-4bb6-90d9-e1db155a914b
-- title:
--   Light Radix Rows: program meets
-- statement:
--   The Light Radix Rows construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean#L123-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixRows.lean#L123-L136

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixRows
open Light RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRadixRows.program_meets {srcBase srcPrev dst p U V : ℕ} {μ : ℕ → ℤ}
    (base prev : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hbaseEnd : srcBase+base.length ≤ dst) (hprevEnd : srcPrev+prev.length ≤ dst)
    (hspace : dst+base.length*prev.length ≤ lim.space)
    (hword : (word p U V : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hbaseRead : Seg μ srcBase base) (hprevRead : Seg μ srcPrev prev)
    (hbaseBound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hprevBound : ∀ y ∈ prev, |y| ≤ (V : ℤ)) :
    Meets lim program 0 d [srcBase,srcPrev,dst,base.length,prev.length,p] μ
      (time base.length prev.length)
      (fun _ ν => Seg ν dst (step (p : ℤ) base prev) ∧
        SameOutside μ ν dst (base.length*prev.length)) := by sorry
