-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_of_ne
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fn_hom_of_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:41:09.734358+00:00
-- url     : https://prove2.me/theorems/d5ee526c-6c66-49fd-a17b-7b5645104b0d
-- title:
--   Y: fn hom of ne
-- statement:
--   The Y construction uses the fn hom of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatNullA.lean#L30-L45

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fn_hom_of_ne {a : ℂ} (ha : a ≠ 0) (b : Fin n → ℂ) :
    fnHom De a b = a ^ (De.totalDegree + 1) * MvPolynomial.eval (fun k => b k / a) De := by sorry
