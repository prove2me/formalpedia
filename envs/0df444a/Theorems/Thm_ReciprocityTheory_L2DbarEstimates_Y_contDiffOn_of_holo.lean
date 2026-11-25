-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_contDiffOn_of_holo
-- name    : ReciprocityTheory.L2DbarEstimates.Y.contDiffOn_of_holo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:56.417827+00:00
-- url     : https://prove2.me/theorems/c4da2922-0fdc-4737-9278-c9ede7bac29f
-- title:
--   Y: cont Diff On of holo
-- statement:
--   The Y construction uses the cont Diff On of holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxC.lean#L25-L27

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

theorem ReciprocityTheory.L2DbarEstimates.Y.contDiffOn_of_holo {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ g U := by sorry
