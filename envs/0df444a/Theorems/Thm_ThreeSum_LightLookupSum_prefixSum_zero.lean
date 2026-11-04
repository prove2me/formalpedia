-- Prove2me | Theorems.Thm_ThreeSum_LightLookupSum_prefixSum_zero
-- name    : ThreeSum.LightLookupSum.prefixSum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:30.991112+00:00
-- url     : https://prove2.me/theorems/b845fd4a-bcb8-4472-ac72-a42530064331
-- title:
--   Light Lookup Sum: prefix Sum zero
-- statement:
--   The Light Lookup Sum construction uses the prefix Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean#L20-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean#L20-L21

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightLookupSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators

theorem ThreeSum.LightLookupSum.prefixSum_zero (f key : ℕ → ℕ) : prefixSum f key 0 = 0 := by sorry
