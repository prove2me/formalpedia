-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_mem_negClassList
-- name    : ThreeSum.ColorClassLists.mem_negClassList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:26.695662+00:00
-- url     : https://prove2.me/theorems/c54fd214-b709-4ea0-b398-b857a9c22ad8
-- title:
--   Color Class Lists: mem neg Class List
-- statement:
--   The Color Class Lists construction uses the mem neg Class List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L40-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L40-L49

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter

theorem ThreeSum.ColorClassLists.mem_negClassList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) (z : ℤ) :
    z ∈ classList p x 2 (-1) ↔ z ∈ Coloring.negValues x (indexColor p) := by sorry
