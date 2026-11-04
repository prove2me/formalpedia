-- Prove2me | Theorems.Thm_ThreeSum_LightClassFilter_mem_items
-- name    : ThreeSum.LightClassFilter.mem_items
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:26:55.786811+00:00
-- url     : https://prove2.me/theorems/238d2d4e-87a5-4f20-ad76-230634e5912d
-- title:
--   Light Class Filter: mem items
-- statement:
--   The Light Class Filter construction uses the mem items property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightClassFilter.lean#L33-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightClassFilter.lean#L33-L35

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightClassFilter
set_option autoImplicit false
open ThreeSum ThreeSum.LightClassFilter
open Light
set_option maxHeartbeats 1200000

theorem ThreeSum.LightClassFilter.mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by sorry
