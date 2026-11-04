-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_reduction_correct_w3sum_ac885d1
-- name    : ThreeSum.ColorClassLists.reduction_correct_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:54.620491+00:00
-- url     : https://prove2.me/theorems/d01982f6-6254-4428-a6e2-7c5acaa472cf
-- title:
--   Color Class Lists: reduction correct
-- statement:
--   Every original distinct-position zero sum appears in one of the actual
--   list triples, for any machine-computed sufficient width.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L100-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L100-L119

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Theorems.Thm_ThreeSum_Coloring_reduction_correct

set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter

theorem ThreeSum.ColorClassLists.reduction_correct_w3sum_ac885d1 {n W : ℕ} (x : Fin n → ℤ) (hn : n ≤ 2^W) :
    Coloring.DistinctZeroSum x ↔ ∃ p : Coloring.Parameter W, witness p x := by sorry
