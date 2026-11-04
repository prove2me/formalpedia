-- Prove2me | Theorems.Thm_ThreeSum_LightLookupSum_prefixSum_le
-- name    : ThreeSum.LightLookupSum.prefixSum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:28.308558+00:00
-- url     : https://prove2.me/theorems/5a4964a5-a8f6-49ec-8612-c382fd1b3446
-- title:
--   Light Lookup Sum: prefix Sum le
-- statement:
--   The Light Lookup Sum construction uses the prefix Sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean#L27-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean#L27-L35

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightLookupSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators

theorem ThreeSum.LightLookupSum.prefixSum_le (f key : ℕ → ℕ) {n B j : ℕ}
    (hvalue : ∀ i < n, f (key i) ≤ B) (hj : j ≤ n) :
    prefixSum f key j ≤ j*B := by sorry
