-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_count_zero_iff
-- name    : ThreeSum.LightTernaryFrozenQuery.count_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:19.029485+00:00
-- url     : https://prove2.me/theorems/ae77bdb8-a786-410d-9c52-7f19251ee34b
-- title:
--   Light Ternary Frozen Query: count zero iff
-- statement:
--   The physical result can be consumed as an exact zero/nonzero decision for
--   original source pairs; factorial scaling is always strictly positive.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPhysical.lean#L148-L156
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPhysical.lean#L148-L156

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryMain
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryFrozenQuery.count_zero_iff {N a b : ℕ} (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
      (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
      ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q=0 ↔
      ThreeSum.TernaryConvolution.convolution f g Q=0 := by sorry
