-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviV_const_mul
-- name    : ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:34.305597+00:00
-- url     : https://prove2.me/theorems/ea7572e0-0b12-4f15-a865-d221c5198835
-- title:
--   Y: levi V const mul
-- statement:
--   The Y construction uses the levi V const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean#L11-L19

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul {n : ℕ} {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (c d : ℝ)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y + d : ℝ) : ℂ)) x ξ = c * leviV n (fun y => ((f y : ℝ) : ℂ)) x ξ := by sorry
