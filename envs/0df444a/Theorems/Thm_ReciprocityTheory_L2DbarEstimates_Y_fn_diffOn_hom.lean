-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_diffOn_hom
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fn_diffOn_hom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:47.664234+00:00
-- url     : https://prove2.me/theorems/e06032fb-f90d-46bf-92e9-84fdb3c6ab03
-- title:
--   Y: fn diff On hom
-- statement:
--   The Y construction uses the fn diff On hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L66-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L66-L83

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fn_diffOn_hom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    {a : E → ℂ} {b : Fin n → E → ℂ} (ha : DifferentiableOn ℂ a S)
    (hb : ∀ k, DifferentiableOn ℂ (b k) S) :
    DifferentiableOn ℂ (fun x => fnHom De (a x) (fun k => b k x)) S := by sorry
