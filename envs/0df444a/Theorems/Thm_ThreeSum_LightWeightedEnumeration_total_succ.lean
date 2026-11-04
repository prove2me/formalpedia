-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEnumeration_total_succ
-- name    : ThreeSum.LightWeightedEnumeration.total_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:19.075559+00:00
-- url     : https://prove2.me/theorems/d1dd36b8-ea08-4512-8ee8-54612fb74a51
-- title:
--   Light Weighted Enumeration: total succ
-- statement:
--   The Light Weighted Enumeration construction uses the total succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L25-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L25-L27

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedEnumeration.total_succ (weights : ℕ → ℕ) (L : ℕ) :
    total weights (L+1) = total weights L+weights L := by sorry
