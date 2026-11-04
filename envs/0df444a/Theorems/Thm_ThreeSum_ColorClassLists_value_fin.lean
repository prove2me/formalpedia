-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_value_fin
-- name    : ThreeSum.ColorClassLists.value_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:36:42.77624+00:00
-- url     : https://prove2.me/theorems/1cc77cae-4633-4954-b864-10af5b8faf9c
-- title:
--   Color Class Lists: value fin
-- statement:
--   The Color Class Lists construction uses the value fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L18-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L18-L19

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter

theorem ThreeSum.ColorClassLists.value_fin {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : value x i.val = x i := by sorry
