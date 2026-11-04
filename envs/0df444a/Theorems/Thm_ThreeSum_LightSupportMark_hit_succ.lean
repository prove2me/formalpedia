-- Prove2me | Theorems.Thm_ThreeSum_LightSupportMark_hit_succ
-- name    : ThreeSum.LightSupportMark.hit_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:22.125031+00:00
-- url     : https://prove2.me/theorems/71ce5f17-63de-4d31-ac58-7ef86b14c638
-- title:
--   Light Support Mark: hit succ
-- statement:
--   The Light Support Mark construction uses the hit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L28-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L28-L38

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
set_option autoImplicit false
open ThreeSum ThreeSum.LightSupportMark
open Light Finset

theorem ThreeSum.LightSupportMark.hit_succ (key valid : ℕ → ℕ) (r i : ℕ) :
    Hit key valid r (i+1) ↔ Hit key valid r i ∨ (valid i=1 ∧ key i=r) := by sorry
