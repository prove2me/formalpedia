-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_diffOn_prod
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fn_diffOn_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:35.275169+00:00
-- url     : https://prove2.me/theorems/7e86f598-49fd-4180-98ec-3575c143bc75
-- title:
--   Y: fn diff On prod
-- statement:
--   The Y construction uses the fn diff On prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L53-L64

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} (De : MvPolynomial (Fin n) ℂ)

theorem ReciprocityTheory.L2DbarEstimates.Y.fn_diffOn_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (u : Finset (Fin n)) (f : Fin n → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (f k) S) :
    DifferentiableOn ℂ (fun x => ∏ k ∈ u, f k x) S := by sorry
