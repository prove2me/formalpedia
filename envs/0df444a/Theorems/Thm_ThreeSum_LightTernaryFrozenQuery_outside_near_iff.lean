-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_outside_near_iff
-- name    : ThreeSum.LightTernaryFrozenQuery.outside_near_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:23.169206+00:00
-- url     : https://prove2.me/theorems/3352f2d8-6051-4e1c-99ee-f1c5ec8a2249
-- title:
--   Light Ternary Frozen Query: outside near iff
-- statement:
--   For an outside-bank target, the actual memo enumerator has exactly the
--   lower words that remain outside the bank.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPhysical.lean#L181-L190
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPhysical.lean#L181-L190

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryMain
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryFrozenQuery.outside_near_iff {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<rank Q) :
    R∈ThreeSum.TernaryBank.nearWords Q (rank Q-(T+1)) ↔ Below R Q ∧ T<rank R := by sorry
