-- Prove2me | Theorems.Thm_ThreeSum_LightClassFilter_program_meets
-- name    : ThreeSum.LightClassFilter.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:36.538352+00:00
-- url     : https://prove2.me/theorems/f498de7e-a9f0-46ed-9ef1-866fdd0d4d2e
-- title:
--   Light Class Filter: program meets
-- statement:
--   The Light Class Filter construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightClassFilter.lean#L131-L143
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightClassFilter.lean#L131-L143

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightClassFilter
set_option autoImplicit false
open ThreeSum ThreeSum.LightClassFilter
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightClassFilter.program_meets {src colors dst n want U : ℕ} {scale : ℤ} {μ : ℕ → ℤ}
    (x : ℕ → ℤ) (color : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (h3 : (3 : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ dst) (hcolors : colors+n ≤ dst) (hspace : dst+(n+1) ≤ lim.space)
    (hwant : want < 3) (hscale : |scale| ≤ 1) (hU : (U : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = x i)
    (hcolorRead : ∀ i < n, μ (colors+i) = (color i : ℤ))
    (hcolorLt : ∀ i < n, color i < 3) (hbound : ∀ i < n, |x i| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,colors,dst,n,want,scale] μ (time n)
      (fun r ν => r = ((items x color want scale n).length : ℤ) ∧
        ν dst = ((items x color want scale n).length : ℤ) ∧
        Seg ν (dst+1) (items x color want scale n) ∧ SameOutside μ ν dst (n+1)) := by sorry
