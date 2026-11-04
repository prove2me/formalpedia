-- Prove2me | Theorems.Thm_ThreeSum_LightWantedRow_meets_w3sum_ac885d1
-- name    : ThreeSum.LightWantedRow.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:24.053964+00:00
-- url     : https://prove2.me/theorems/e1f73a9a-e427-489f-81f7-6243174691ad
-- title:
--   Light Wanted Row: meets
-- statement:
--   The Light Wanted Row construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedRow.lean#L33-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedRow.lean#L33-L82

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightWantedRow
set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedRow
open Light
set_option maxHeartbeats 900000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWantedRow.meets_w3sum_ac885d1 {pMain left src start n dst previous : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+start+n ≤ dst) (hspace : dst+2*(previous+n) ≤ lim.space)
    (hleft : (left : ℤ) ≤ lim.word)
    (hvalues : ∀ t < n, |μ (src+start+t)| ≤ lim.word) :
    Meets lim P pMain d [left,src,start,n,dst,previous] μ (time n)
      (fun _ ν => (∀ t < n, ν (dst+2*(previous+t))=(left : ℤ) ∧
        ν (dst+2*(previous+t)+1)=μ (src+start+t)) ∧
        SameOutside μ ν (dst+2*previous) (2*n)) := by sorry
