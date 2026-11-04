-- Prove2me | Theorems.Thm_ThreeSum_LightArray_source_read
-- name    : ThreeSum.LightArray.source_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:21:51.033264+00:00
-- url     : https://prove2.me/theorems/930fe2c8-82eb-4720-acd2-004b151a24eb
-- title:
--   Light Array: source read
-- statement:
--   The Light Array construction uses the source read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L21-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightArray.lean#L21-L26

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightArray.source_read {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : SourceSafe src dst n) (hj : j < n) :
    wrote μ dst f j (src + j) = μ (src + j) := by sorry
