-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_stageValue_count
-- name    : ThreeSum.LightTernaryFrozenQuery.stageValue_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:42.009256+00:00
-- url     : https://prove2.me/theorems/5500e0b7-0351-49ae-9ec0-c401eaa608a3
-- title:
--   Light Ternary Frozen Query: stage Value count
-- statement:
--   Full-stage query output is the original additive convolution, scaled by the
--   positive factorial of the physical target word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPhysical.lean#L132-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPhysical.lean#L132-L144

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryMain
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryFrozenQuery.stageValue_count {N a b : ℕ} (f g : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    stageValue N (fun R => ThreeSum.TernaryEuler.binomialZeta
      (fun A => ThreeSum.TernaryConvolution.factorial A*f A) R *
      ThreeSum.TernaryEuler.binomialZeta (fun B => ThreeSum.TernaryConvolution.factorial B*g B) R) Q =
      ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q := by sorry
