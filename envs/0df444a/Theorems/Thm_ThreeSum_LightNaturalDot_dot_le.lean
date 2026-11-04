-- Prove2me | Theorems.Thm_ThreeSum_LightNaturalDot_dot_le
-- name    : ThreeSum.LightNaturalDot.dot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:37.415877+00:00
-- url     : https://prove2.me/theorems/68e29e73-652f-4ccf-91f0-b18cd26a0947
-- title:
--   Light Natural Dot: dot le
-- statement:
--   The Light Natural Dot construction uses the dot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNaturalDot.lean#L13-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightNaturalDot.lean#L13-L23

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_le

set_option autoImplicit false
open ThreeSum ThreeSum.LightNaturalDot
open Light Finset
open scoped BigOperators

theorem ThreeSum.LightNaturalDot.dot_le (f g : ℕ → ℕ) {n j U V : ℕ}
    (hf : ∀ i<n, f i≤U) (hg : ∀ i<n, g i≤V) (hj : j≤n) :
    dot f g j≤j*(U*V) := by sorry
