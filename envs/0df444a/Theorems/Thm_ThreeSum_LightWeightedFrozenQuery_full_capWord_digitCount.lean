-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_full_capWord_digitCount
-- name    : ThreeSum.LightWeightedFrozenQuery.full_capWord_digitCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:25.069572+00:00
-- url     : https://prove2.me/theorems/af4eec37-0d03-438e-92bb-bd99b0f6b449
-- title:
--   Light Weighted Frozen Query: full cap Word digit Count
-- statement:
--   The Light Weighted Frozen Query construction uses the full cap Word digit Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L74-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenTime.lean#L74-L77

import Definitions.Def_Submission_Weighted_FrozenPrepare
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedFrozenQueryCost
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedFrozenQuery.full_capWord_digitCount {N : ℕ} (R : TritWord N) (d : Fin 3) :
    digitCount (capWord (coords N N) R) d=digitCount R d := by sorry
