-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_zLoc_chart
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fc_zLoc_chart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:38:34.031571+00:00
-- url     : https://prove2.me/theorems/f1fe774b-df0b-4191-bcab-403cb6296759
-- title:
--   Y: fc z Loc chart
-- statement:
--   The Y construction uses the fc z Loc chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcB.lean#L218-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcB.lean#L218-L223

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcB
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
universe u

theorem ReciprocityTheory.L2DbarEstimates.Y.fc_zLoc_chart {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s)
    (e : OpenPartialHomeomorph (A.Mset w0 s De) (V n)) (he : IsChart n (fun y : A.Mset w0 s De => A.zmap w0 s y) e)
    (x : A.Mset w0 s De) (hxe : x ∈ e.source) (i : ι) (hxi : (x : Y) ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i x) = e x := by sorry
