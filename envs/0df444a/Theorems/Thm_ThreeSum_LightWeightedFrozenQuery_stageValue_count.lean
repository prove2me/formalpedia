-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_stageValue_count
-- name    : ThreeSum.LightWeightedFrozenQuery.stageValue_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:04:11.49173+00:00
-- url     : https://prove2.me/theorems/80c884e6-bd3d-498e-8f0b-e3f7a7f50ca0
-- title:
--   Light Weighted Frozen Query: stage Value count
-- statement:
--   Full-stage query output is the original additive convolution, scaled by the
--   positive factorial of the physical target word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenPhysical.lean#L145-L157
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenPhysical.lean#L145-L157

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

theorem ThreeSum.LightWeightedFrozenQuery.stageValue_count {N a b : ℕ} (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
      (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
      ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q =
      ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q := by sorry
