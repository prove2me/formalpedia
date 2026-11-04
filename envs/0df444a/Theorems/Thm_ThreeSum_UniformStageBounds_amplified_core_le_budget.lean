-- Prove2me | Theorems.Thm_ThreeSum_UniformStageBounds_amplified_core_le_budget
-- name    : ThreeSum.UniformStageBounds.amplified_core_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:17.234681+00:00
-- url     : https://prove2.me/theorems/be9f471f-2b14-4751-bef2-2340d5057fd8
-- title:
--   Uniform Stage Bounds: amplified core le budget
-- statement:
--   The Uniform Stage Bounds construction uses the amplified core le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean#L129-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/UniformStageBounds.lean#L129-L138

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

theorem ThreeSum.UniformStageBounds.amplified_core_le_budget {n C k W H P H1 : ℕ}
    (hW : W * radix n ≤ wantedNumerator n)
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) :
    amplifiedCoreWork C (fun _ => W) (fun _ => H) n ≤ workBudget C k n := by sorry
