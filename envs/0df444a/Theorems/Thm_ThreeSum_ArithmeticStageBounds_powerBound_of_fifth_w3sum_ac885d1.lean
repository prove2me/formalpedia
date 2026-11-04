-- Prove2me | Theorems.Thm_ThreeSum_ArithmeticStageBounds_powerBound_of_fifth_w3sum_ac885d1
-- name    : ThreeSum.ArithmeticStageBounds.powerBound_of_fifth_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:43:51.269688+00:00
-- url     : https://prove2.me/theorems/fb978427-dbbb-434a-a1cf-5fd6ce02076f
-- title:
--   Arithmetic Stage Bounds: power Bound of fifth
-- statement:
--   An exact integer fifth-power estimate supplies the real exponent bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean#L81-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ArithmeticStageBounds.lean#L81-L104

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
noncomputable section

theorem ThreeSum.ArithmeticStageBounds.powerBound_of_fifth_w3sum_ac885d1 {f g : ℕ → ℕ} {a : ℝ}
    (hg : PowerBound g a) (hfg : ∀ n, f n^5 ≤ 256*g n^8) :
    PowerBound f ((8/5)*a) := by sorry
