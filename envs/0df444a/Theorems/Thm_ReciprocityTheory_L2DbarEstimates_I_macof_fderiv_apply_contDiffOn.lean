-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_macof_fderiv_apply_contDiffOn
-- name    : ReciprocityTheory.L2DbarEstimates.I.macof_fderiv_apply_contDiffOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:10.5456+00:00
-- url     : https://prove2.me/theorems/53b85772-39f6-4202-8f06-3ad6018d01fb
-- title:
--   I: macof fderiv apply cont Diff On
-- statement:
--   The I construction uses the macof fderiv apply cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/MacofFderivApplyContDiffOn.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/MacofFderivApplyContDiffOn.lean#L13-L14

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_MacofFderivApplyContDiffOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.macof_fderiv_apply_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (u : V n) : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y u) U := by sorry
