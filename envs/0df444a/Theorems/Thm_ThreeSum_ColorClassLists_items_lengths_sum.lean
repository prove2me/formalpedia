-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_items_lengths_sum
-- name    : ThreeSum.ColorClassLists.items_lengths_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:36.186059+00:00
-- url     : https://prove2.me/theorems/54d3172c-f0c2-4e77-a718-530e1b06081e
-- title:
--   Color Class Lists: items lengths sum
-- statement:
--   The Color Class Lists construction uses the items lengths sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L55-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L55-L64

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter

theorem ThreeSum.ColorClassLists.items_lengths_sum (x : ℕ → ℤ) (color : ℕ → ℕ) (hcolor : ∀ i, color i < 3) (n : ℕ) :
    (items x color 0 1 n).length + (items x color 1 1 n).length +
      (items x color 2 (-1) n).length = n := by sorry
