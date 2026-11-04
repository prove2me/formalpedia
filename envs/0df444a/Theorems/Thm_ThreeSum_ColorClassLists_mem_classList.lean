-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_mem_classList
-- name    : ThreeSum.ColorClassLists.mem_classList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:23.75268+00:00
-- url     : https://prove2.me/theorems/6a1a67b9-c7de-4807-9c82-b848e2e97a6e
-- title:
--   Color Class Lists: mem class List
-- statement:
--   The Color Class Lists construction uses the mem class List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L28-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L28-L38

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter

theorem ThreeSum.ColorClassLists.mem_classList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : Fin 3) (z : ℤ) :
    z ∈ classList p x c.val 1 ↔ z ∈ Coloring.values x (indexColor p) c := by sorry
