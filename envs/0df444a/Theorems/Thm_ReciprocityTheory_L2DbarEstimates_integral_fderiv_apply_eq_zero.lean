-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_fderiv_apply_eq_zero
-- name    : ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:54.234099+00:00
-- url     : https://prove2.me/theorems/56c21201-5db6-4488-9341-0d73415107f0
-- title:
--   L2 Dbar Estimates: integral fderiv apply eq zero
-- statement:
--   The L2 Dbar Estimates construction uses the integral fderiv apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L11-L20

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
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

theorem ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero (n : ℕ) (H : V n → ℂ) (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) (v : V n) : ∫ y, fderiv ℝ H y v = 0 := by sorry
