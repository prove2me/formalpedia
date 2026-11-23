-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_comm_fderiv_apply
-- name    : ReciprocityTheory.L2DbarEstimates.comm_fderiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:19.297847+00:00
-- url     : https://prove2.me/theorems/10640972-5310-4ea9-8f1c-311bcbcc378d
-- title:
--   L2 Dbar Estimates: comm fderiv apply
-- statement:
--   The L2 Dbar Estimates construction uses the comm fderiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L10-L15

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.comm_fderiv_apply {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (u : V n) :
    HasFDerivAt (fun y' => fderiv ℝ g y' u)
      ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ g) y)) y := by sorry
