-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_digitCount_wordList
-- name    : ThreeSum.LightWeightedFrozenQuery.digitCount_wordList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:09.308821+00:00
-- url     : https://prove2.me/theorems/aca1f933-81d4-4506-bdf8-c3509ead8e49
-- title:
--   Light Weighted Frozen Query: digit Count word List
-- statement:
--   The Light Weighted Frozen Query construction uses the digit Count word List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L62-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L62-L65

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedFrozenQuery.digitCount_wordList {N : ℕ} (R : TritWord N) (d : Fin 3) :
    digitCount R d=((WeightedBankEnumeration.wordList R).map
      (fun a : ℕ => if a=d.val then 1 else 0)).sum := by sorry
