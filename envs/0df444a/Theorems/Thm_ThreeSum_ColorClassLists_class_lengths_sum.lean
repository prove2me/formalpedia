-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_class_lengths_sum
-- name    : ThreeSum.ColorClassLists.class_lengths_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:42.615761+00:00
-- url     : https://prove2.me/theorems/4f264ee5-a665-4813-b141-0042aa6e2b73
-- title:
--   Color Class Lists: class lengths sum
-- statement:
--   The Color Class Lists construction uses the class lengths sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L66-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L66-L69

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter

theorem ThreeSum.ColorClassLists.class_lengths_sum {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) :
    (classList p x 0 1).length + (classList p x 1 1).length +
      (classList p x 2 (-1)).length = n := by sorry
