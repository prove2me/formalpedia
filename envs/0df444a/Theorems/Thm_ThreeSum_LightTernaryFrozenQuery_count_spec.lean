-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_count_spec
-- name    : ThreeSum.LightTernaryFrozenQuery.count_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:29.897444+00:00
-- url     : https://prove2.me/theorems/164115fd-61cf-4c1a-a7d7-7a94e2686114
-- title:
--   Light Ternary Frozen Query: count spec
-- statement:
--   Rewrite an actual full query execution contract to the exact source-count
--   contract, retaining the same program, time bound and preserved memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPhysical.lean#L160-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPhysical.lean#L160-L171

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryMain
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryFrozenQuery.count_spec {N a b pMain d time : ℕ} (args : List ℤ) (μ : ℕ→ℤ)
    (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b)
    (hquery : Meets lim P pMain d args μ time (fun v μ' =>
      v=stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
        (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
        ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q ∧ μ'=μ)) :
    Meets lim P pMain d args μ time (fun v μ' =>
      v=ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q ∧ μ'=μ) := by sorry
