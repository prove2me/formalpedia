-- Prove2me | Theorems.Thm_ThreeSum_LightNormalize_sorted_head_not_mem
-- name    : ThreeSum.LightNormalize.sorted_head_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:29.359936+00:00
-- url     : https://prove2.me/theorems/5b95494a-1686-487a-a278-e742675ef2f9
-- title:
--   Light Normalize: sorted head not mem
-- statement:
--   The Light Normalize construction uses the sorted head not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L38-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L38-L44

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightNormalize.sorted_head_not_mem {x y : ℤ} {zs : List ℤ}
    (hs : (x::y::zs).Pairwise (· ≤ ·)) (hne : x ≠ y) : x ∉ y::zs := by sorry
