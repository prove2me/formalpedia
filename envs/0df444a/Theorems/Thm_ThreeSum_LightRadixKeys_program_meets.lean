-- Prove2me | Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
-- name    : ThreeSum.LightRadixKeys.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:24.694854+00:00
-- url     : https://prove2.me/theorems/65a92852-a956-4b2f-883d-dd3fb3a6f646
-- title:
--   Light Radix Keys: program meets
-- statement:
--   The Light Radix Keys construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L203-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L203-L213

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightRadixKeys.program_meets {src dst p U J d : ℕ} {μ : ℕ → ℤ}
    (base : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+base.length ≤ dst) (hm : 0 < base.length)
    (hbound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hspace : space dst base.length J ≤ lim.space) (hword : (word p U J : ℤ) ≤ lim.word)
    (hd : d+J+2 ≤ lim.depth) (hread : Seg μ src base) :
    Meets lim program 0 d [src,base.length,J,p,dst] μ (time base.length J)
      (fun r ν => r = ((dst+offset base.length J : ℕ) : ℤ) ∧
        ν (dst+offset base.length J) = ((base.length^J : ℕ) : ℤ) ∧
        Seg ν (dst+offset base.length J+1) (values (p : ℤ) base J) ∧ Kept μ ν dst) := by sorry
