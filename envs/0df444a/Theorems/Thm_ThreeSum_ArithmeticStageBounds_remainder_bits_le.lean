-- Prove2me | Theorems.Thm_ThreeSum_ArithmeticStageBounds_remainder_bits_le
-- name    : ThreeSum.ArithmeticStageBounds.remainder_bits_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:31.730166+00:00
-- url     : https://prove2.me/theorems/b3e094d3-c212-4ebe-aacf-b8a9afaaef1c
-- title:
--   Arithmetic Stage Bounds: remainder bits le
-- statement:
--   The Arithmetic Stage Bounds construction uses the remainder bits le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean#L52-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean#L52-L60

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000

theorem ThreeSum.ArithmeticStageBounds.remainder_bits_le {n : ℕ} (k : ℕ) (hn : 0 < n) :
    Nat.log 2 (n^k+1)+1 ≤ bitBudget k n := by sorry
