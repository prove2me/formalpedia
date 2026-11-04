-- Prove2me | Theorems.Thm_ThreeSum_ArithmeticStageBounds_invocation_le_budget
-- name    : ThreeSum.ArithmeticStageBounds.invocation_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:39.640497+00:00
-- url     : https://prove2.me/theorems/97fa1d0e-44ac-4e3b-9414-1cba78f1b131
-- title:
--   Arithmetic Stage Bounds: invocation le budget
-- statement:
--   The Arithmetic Stage Bounds construction uses the invocation le budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean#L62-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean#L62-L70

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.ArithmeticStageBounds.invocation_le_budget {n p nA nB nC : ℕ} (k : ℕ)
    (hn : 0 < n) (hp : p ≤ maxMod n)
    (ha : nA ≤ bandSize n) (hb : nB ≤ bandSize n) (hc : nC ≤ bandSize n) :
    LightModuloCounts.time p nA nB nC (n^k) ≤ perTripleBudget k n := by sorry
