-- Prove2me | Theorems.Thm_ThreeSum_LightClassFilter_items_succ
-- name    : ThreeSum.LightClassFilter.items_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:45.376209+00:00
-- url     : https://prove2.me/theorems/e73817fd-cc5a-4cb0-b8ac-5f6799775ffe
-- title:
--   Light Class Filter: items succ
-- statement:
--   The Light Class Filter construction uses the items succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightClassFilter.lean#L23-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightClassFilter.lean#L23-L26

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightClassFilter
set_option autoImplicit false
open ThreeSum ThreeSum.LightClassFilter
open Light
set_option maxHeartbeats 1200000

theorem ThreeSum.LightClassFilter.items_succ (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    items x color want scale (n+1) =
      items x color want scale n ++ (if color n = want then [scale*x n] else []) := by sorry
