-- Prove2me | Theorems.Thm_ThreeSum_LightNormalize_dedup_strict
-- name    : ThreeSum.LightNormalize.dedup_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:10:27.519742+00:00
-- url     : https://prove2.me/theorems/49ce7238-9a33-4f26-84c7-ab006fef8059
-- title:
--   Light Normalize: dedup strict
-- statement:
--   The Light Normalize construction uses the dedup strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L46-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNormalize.lean#L46-L50

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize
set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightNormalize.dedup_strict {L : List ℤ} (hs : L.Pairwise (· ≤ ·)) :
    L.dedup.Pairwise (· < ·) := by sorry
