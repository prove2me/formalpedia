-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_step
-- name    : ThreeSum.LightWeightedFrozenQuery.queryTime_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:03.651221+00:00
-- url     : https://prove2.me/theorems/8f64de42-26de-4f7c-b644-ca0728cfcb3e
-- title:
--   Light Weighted Frozen Query: query Time step
-- statement:
--   The Light Weighted Frozen Query construction uses the query Time step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L37-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L37-L53

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenTime
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedFrozenQuery.queryTime_step {N K : ℕ} (L T : ℕ) (R : TritWord N) (hK : K<N)
    (hbank : T<cacheCost R) :
    let i : Fin N :=⟨K,hK⟩
    let t := fun d : Fin 3 => if d≤R i then queryTime L T K (Function.update R i d) else 0
    prepTime N+(t 0+t 1+t 2+200)≤queryTime L T (K+1) R := by sorry
