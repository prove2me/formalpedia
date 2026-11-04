-- Prove2me | Theorems.Thm_ThreeSum_LightSupportMark_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSupportMark.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:41.282668+00:00
-- url     : https://prove2.me/theorems/83d3a6ac-0e17-43d9-9597-bec1be940b76
-- title:
--   Light Support Mark: meets
-- statement:
--   The Light Support Mark construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L123-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L123-L152

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
set_option autoImplicit false
open ThreeSum ThreeSum.LightSupportMark
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSupportMark.meets_w3sum_ac885d1 {pMain pFill : ℕ}
    (hmain : P[pMain]? = some (body pFill)) (hfill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {keys flags dst n p : ℕ}
    (key valid : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hK : keys+n ≤ lim.space) (hF : flags+n ≤ lim.space) (hD : dst+p ≤ lim.space)
    (hsepK : Apart keys n dst p) (hsepF : Apart flags n dst p)
    (hkeys : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags+i) = (valid i : ℤ))
    (hkeyLt : ∀ i < n, key i < p) (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [keys,flags,dst,n,p] μ (time n p)
      (fun _ μ' => (∀ r < p, μ' (dst+r) = (bit key valid r n : ℤ)) ∧
        SameOutside μ μ' dst p) := by sorry
