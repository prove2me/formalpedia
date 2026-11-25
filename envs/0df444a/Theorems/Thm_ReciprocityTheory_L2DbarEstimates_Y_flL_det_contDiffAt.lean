-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flL_det_contDiffAt
-- name    : ReciprocityTheory.L2DbarEstimates.Y.flL_det_contDiffAt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:12:09.654565+00:00
-- url     : https://prove2.me/theorems/0638931c-5b3d-47bc-8a49-477a4b4d9f9f
-- title:
--   Y: fl L det cont Diff At
-- statement:
--   The Y construction uses the fl L det cont Diff At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L153-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLoc.lean#L153-L161

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.flL_det_contDiffAt {G : V n → V n →L[ℂ] V n} {y : V n} (hG : ContDiffAt ℂ ∞ G y) :
    ContDiffAt ℂ ∞ (fun v => (G v).det) y := by sorry
