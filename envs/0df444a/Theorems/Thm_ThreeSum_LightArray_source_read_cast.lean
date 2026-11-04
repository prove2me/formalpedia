-- Prove2me | Theorems.Thm_ThreeSum_LightArray_source_read_cast
-- name    : ThreeSum.LightArray.source_read_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:21:50.428364+00:00
-- url     : https://prove2.me/theorems/3807b151-3faa-49fa-81e8-7f82f0b573b0
-- title:
--   Light Array: source read cast
-- statement:
--   The Light Array construction uses the source read cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L28-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L28-L34

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightArray.source_read_cast {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : SourceSafe src dst n) (hj : j < n) :
    wrote μ dst f j ((src : ℤ) + (j : ℤ)).toNat = μ (src + j) := by sorry
