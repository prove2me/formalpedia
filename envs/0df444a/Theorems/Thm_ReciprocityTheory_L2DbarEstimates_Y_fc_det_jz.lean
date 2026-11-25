-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_det_jz
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fc_det_jz
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:38:09.791794+00:00
-- url     : https://prove2.me/theorems/b58dd4a1-8b86-548a-9e1e-f0dbd9b2e8d8
-- title:
--   Y: fc det jz
-- statement:
--   The Y construction uses the fc det jz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcB.lean#L147-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcB.lean#L147-L182

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fc_det_jz {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i j : ι) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) :
    (fderiv ℂ (A.zLoc w0 s i) (A.chart i y)).det = (fderiv ℂ (A.zLoc w0 s j) (A.chart j y)).det * A.g A.kap i j y := by sorry
