-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_full_capWord_list
-- name    : ThreeSum.LightWeightedFrozenQuery.full_capWord_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:28:19.718838+00:00
-- url     : https://prove2.me/theorems/c26ce4a4-26b9-4609-9568-47872b57f3db
-- title:
--   Light Weighted Frozen Query: full cap Word list
-- statement:
--   The Light Weighted Frozen Query construction uses the full cap Word list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L67-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L67-L72

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedFrozenQuery.full_capWord_list {N : ℕ} (R : TritWord N) :
    WeightedBankEnumeration.wordList (capWord (coords N N) R)=
      (WeightedBankEnumeration.wordList R).reverse := by sorry
