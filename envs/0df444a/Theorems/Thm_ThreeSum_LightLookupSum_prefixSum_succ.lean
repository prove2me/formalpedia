-- Prove2me | Theorems.Thm_ThreeSum_LightLookupSum_prefixSum_succ
-- name    : ThreeSum.LightLookupSum.prefixSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:23.991488+00:00
-- url     : https://prove2.me/theorems/94796d3b-44dd-41fd-8262-95ded131a35a
-- title:
--   Light Lookup Sum: prefix Sum succ
-- statement:
--   The Light Lookup Sum construction uses the prefix Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean#L23-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLookupSum.lean#L23-L25

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightLookupSum
set_option autoImplicit false
open ThreeSum ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators

theorem ThreeSum.LightLookupSum.prefixSum_succ (f key : ℕ → ℕ) (j : ℕ) :
    prefixSum f key (j+1) = prefixSum f key j + f (key j) := by sorry
