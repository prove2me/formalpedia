-- Prove2me | Theorems.Thm_ThreeSum_UniformStageBounds_false_le_budget
-- name    : ThreeSum.UniformStageBounds.false_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:09.591207+00:00
-- url     : https://prove2.me/theorems/6468de2b-a518-4fee-bd09-85d8a28b3b6f
-- title:
--   Uniform Stage Bounds: false le budget
-- statement:
--   The Uniform Stage Bounds construction uses the false le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean#L37-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean#L37-L44

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.UniformStageBounds.false_le_budget {n k P H H1 : ℕ}
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) : H ≤ falseBudget k n := by sorry
