-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_queryTime_step
-- name    : ThreeSum.LightTernaryFrozenQuery.queryTime_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:27.044223+00:00
-- url     : https://prove2.me/theorems/d57e9594-ef0a-4915-b653-5184a7095c57
-- title:
--   Light Ternary Frozen Query: query Time step
-- statement:
--   The Light Ternary Frozen Query construction uses the query Time step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L31-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L31-L47

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.queryTime_step {N K : ℕ} (L T : ℕ) (R : TritWord N) (hK : K<N)
    (hbank : T<rank R) :
    let i : Fin N :=⟨K,hK⟩
    let t := fun d : Fin 3 => if d≤R i then queryTime L T K (Function.update R i d) else 0
    prepTime N+(t 0+t 1+t 2+200)≤queryTime L T (K+1) R := by sorry
