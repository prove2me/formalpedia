-- Prove2me | Theorems.Thm_ThreeSum_LightSupportMark_mark_ends
-- name    : ThreeSum.LightSupportMark.mark_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:34.537442+00:00
-- url     : https://prove2.me/theorems/a0320560-fdf2-4a41-b8af-b8adb564ab94
-- title:
--   Light Support Mark: mark ends
-- statement:
--   The Light Support Mark construction uses the mark ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L66-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L66-L116

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
set_option autoImplicit false
open ThreeSum ThreeSum.LightSupportMark
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSupportMark.mark_ends {μ : ℕ → ℤ} {loc : ℕ → ℤ} {keys flags dst n p : ℕ}
    (key valid : ℕ → ℕ)
    (hkeysLoc : loc 0=keys) (hflagsLoc : loc 1=flags) (hdstLoc : loc 2=dst) (hlen : loc 3=n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hK : keys+n ≤ lim.space) (hF : flags+n ≤ lim.space) (hD : dst+p ≤ lim.space)
    (hsepK : Apart keys n dst p) (hsepF : Apart flags n dst p)
    (hkeys : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags+i) = (valid i : ℤ))
    (hkeyLt : ∀ i < n, key i < p)
    (hzero : ∀ r < p, μ (dst+r)=0) (hword : (1 : ℤ) ≤ lim.word) :
    Ends lim P d markBody ⟨loc,μ⟩ (markTime n)
      (fun σ' => (∀ r < p, σ'.mem (dst+r) = (bit key valid r n : ℤ)) ∧
        SameOutside μ σ'.mem dst p) := by sorry
