-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_full_capWord_digitCount
-- name    : ThreeSum.LightTernaryFrozenQuery.full_capWord_digitCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:36:33.702922+00:00
-- url     : https://prove2.me/theorems/9af4385a-70d1-48fd-8f56-5613a5b5b969
-- title:
--   Light Ternary Frozen Query: full cap Word digit Count
-- statement:
--   The Light Ternary Frozen Query construction uses the full cap Word digit Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L68-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L68-L71

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.full_capWord_digitCount {N : ℕ} (R : TritWord N) (d : Fin 3) :
    digitCount (capWord (coords N N) R) d=digitCount R d := by sorry
