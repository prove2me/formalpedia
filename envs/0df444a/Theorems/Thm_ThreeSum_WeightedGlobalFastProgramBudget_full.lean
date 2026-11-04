-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramBudget_full
-- name    : ThreeSum.WeightedGlobalFastProgramBudget.full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:05:35.831339+00:00
-- url     : https://prove2.me/theorems/4580db62-59b4-4a27-ab31-c228b38c9ca7
-- title:
--   Weighted Global Fast Program Budget: full
-- statement:
--   All actual once-per-input setup and the complete coloring scan retain
--   the child's proved exponent. No caller address enters the time bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramBudget.lean#L37-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramBudget.lean#L37-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramBudget
open Light StageBounds ArithmeticStageBounds LightColorParametersCosts
open Filter
open scoped Topology

theorem ThreeSum.WeightedGlobalFastProgramBudget.full {m b p K κ : ℕ} [Fact p.Prime] (hm : 0<m) (hb : 1<b)
    {T : ℕ→ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 0≤a) :
    PowerBound (fun n=>LightWeightedGlobalFastProgramProof.time (WeightedGlobalCoverScale.outputSize m) b p K κ (T n) n) a := by sorry
