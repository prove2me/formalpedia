-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_eq_zero_of_eval
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fn_eq_zero_of_eval
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:40:43.648831+00:00
-- url     : https://prove2.me/theorems/0921ae7a-bf7a-5c72-8135-43ec35da6274
-- title:
--   Y: fn eq zero of eval
-- statement:
--   The Y construction uses the fn eq zero of eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L85-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L85-L106

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fn_eq_zero_of_eval {v0 : V n}
    (h : ∀ᶠ v in 𝓝 v0, MvPolynomial.eval (fun k => v k) De = 0) : De = 0 := by sorry
