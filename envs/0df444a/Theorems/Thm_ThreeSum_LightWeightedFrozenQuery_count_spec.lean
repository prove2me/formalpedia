-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_count_spec
-- name    : ThreeSum.LightWeightedFrozenQuery.count_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:34.679511+00:00
-- url     : https://prove2.me/theorems/6a93529c-2472-45f0-accf-5bd021f3dd48
-- title:
--   Light Weighted Frozen Query: count spec
-- statement:
--   Rewrite an actual full query execution contract to the exact source-count
--   contract, retaining the same program, time bound and preserved memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenPhysical.lean#L173-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenPhysical.lean#L173-L184

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

theorem ThreeSum.LightWeightedFrozenQuery.count_spec {N a b pMain d time : ℕ} (args : List ℤ) (μ : ℕ→ℤ)
    (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b)
    (hquery : Meets lim P pMain d args μ time (fun v μ' =>
      v=stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
        (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
        ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q ∧ μ'=μ)) :
    Meets lim P pMain d args μ time (fun v μ' =>
      v=ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q ∧ μ'=μ) := by sorry
