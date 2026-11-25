-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_aprb_complement
-- name    : ReciprocityTheory.L2DbarEstimates.Y.aprb_complement
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:40.123361+00:00
-- url     : https://prove2.me/theorems/ac6bdc18-a872-47d5-8228-d61a39a27554
-- title:
--   Y: aprb complement
-- statement:
--   The Y construction uses the aprb complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeB.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeB.lean#L11-L36

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeB
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
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.aprb_complement {n d : ℕ} (Lm : V n →L[ℂ] V d) (hs : Function.Surjective Lm) :
    ∃ A : V n ≃L[ℂ] V d × V (n - d), ∀ v, (A v).1 = Lm v := by sorry
