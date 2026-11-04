-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEnumeration_output_succ
-- name    : ThreeSum.LightWeightedEnumeration.output_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:19.473173+00:00
-- url     : https://prove2.me/theorems/bdb6660f-9944-4c72-a17d-1b583ffaf845
-- title:
--   Light Weighted Enumeration: output succ
-- statement:
--   The Light Weighted Enumeration construction uses the output succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L58-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L58-L61

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_succ
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedEnumeration.output_succ {weights : ℕ → ℕ} {L k : ℕ} (hk : k+1 ≤ L+1) (pref : ℕ) :
    output weights (L+1) (k+1) pref =
      output weights L (k+1) pref ++ output weights L k (pref+weights L) := by sorry
