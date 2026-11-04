-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramBudget_scan
-- name    : ThreeSum.WeightedGlobalFastProgramBudget.scan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:05:31.633411+00:00
-- url     : https://prove2.me/theorems/e5166b72-fa27-434e-8aea-1c87afa900ce
-- title:
--   Weighted Global Fast Program Budget: scan
-- statement:
--   The actual finite coloring enumeration adds only a subpolynomial
--   factor to the running time of the included per-color program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramBudget.lean#L23-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramBudget.lean#L23-L33

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramBudget
open Light StageBounds ArithmeticStageBounds LightColorParametersCosts
open Filter
open scoped Topology

theorem ThreeSum.WeightedGlobalFastProgramBudget.scan {T : ℕ→ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 0≤a) :
    PowerBound (fun n=>LightColorScanHost.time (T n) n) a := by sorry
