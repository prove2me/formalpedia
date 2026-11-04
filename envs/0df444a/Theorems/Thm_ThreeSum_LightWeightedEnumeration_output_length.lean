-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_length
-- name    : ThreeSum.LightWeightedEnumeration.output_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:14.378246+00:00
-- url     : https://prove2.me/theorems/cabd65b7-ee50-4679-b98c-788c85851fdc
-- title:
--   Light Weighted Enumeration: output length
-- statement:
--   The Light Weighted Enumeration construction uses the output length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L37-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L37-L47

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedEnumeration.output_length (weights : ℕ → ℕ) (L k pref : ℕ) :
    (output weights L k pref).length = L.choose k := by sorry
