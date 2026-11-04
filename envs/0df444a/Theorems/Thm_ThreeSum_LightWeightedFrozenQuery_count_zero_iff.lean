-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_count_zero_iff
-- name    : ThreeSum.LightWeightedFrozenQuery.count_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:57.756725+00:00
-- url     : https://prove2.me/theorems/04f8e587-1e44-41f1-8a8f-63fbf4febbe3
-- title:
--   Light Weighted Frozen Query: count zero iff
-- statement:
--   The physical result can be consumed as an exact zero/nonzero decision for
--   original source pairs; factorial scaling is always strictly positive.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenPhysical.lean#L161-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenPhysical.lean#L161-L169

import Definitions.Def_Submission_Weighted_FrozenMain
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_Weighted_FrozenPhysical
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedFrozenQueryCost (cacheCost)
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedFrozenQuery.count_zero_iff {N a b : ℕ} (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
      (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
      ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q=0 ↔
      ThreeSum.TernaryConvolution.convolution f g Q=0 := by sorry
