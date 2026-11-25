-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_diff_comp_apply
-- name    : ReciprocityTheory.L2DbarEstimates.Y.flA_diff_comp_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:54.332824+00:00
-- url     : https://prove2.me/theorems/c30dc40f-d349-46bd-b3c1-9e1ce058a724
-- title:
--   Y: fl A diff comp apply
-- statement:
--   The Y construction uses the fl A diff comp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L76-L81

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.flA_diff_comp_apply {G : V n → V n} {y : V n} (hG : ContDiffAt ℂ 2 G y) (k b : Fin n) :
    DifferentiableAt ℂ (fun v => fderiv ℂ G v (bas n k) b) y := by sorry
