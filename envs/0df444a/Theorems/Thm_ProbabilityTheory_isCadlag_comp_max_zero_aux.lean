-- Prove2me | Theorems.Thm_ProbabilityTheory_isCadlag_comp_max_zero_aux
-- name    : ProbabilityTheory.isCadlag_comp_max_zero_aux
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:44:18.346212+00:00
-- url     : https://prove2.me/theorems/42ef4df4-44c3-449f-8efa-30ef9ce39723
-- title:
--   LeanLevy auxiliary: isCadlag comp max zero
-- statement:
--   Source-private helper used by the LeanLevy small-jump càdlàg convergence argument; lifted verbatim to a separately verifiable proof obligation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/LevyJumpPath.lean#L1237

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

theorem ProbabilityTheory.isCadlag_comp_max_zero_aux {f : ℝ → ℝ} (hf : IsCadlag f) (h0 : f 0 = 0) :
    IsCadlag (fun t : ℝ => f (max t 0)) := by sorry
