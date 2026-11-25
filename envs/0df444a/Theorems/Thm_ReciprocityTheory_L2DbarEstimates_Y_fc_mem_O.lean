-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_mem_O
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fc_mem_O
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:37:43.386034+00:00
-- url     : https://prove2.me/theorems/c2b686a0-e7f2-54ce-bec6-d8c3fbdbc201
-- title:
--   Y: fc mem O
-- statement:
--   The Y construction uses the fc mem O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcB.lean#L225-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcB.lean#L225-L231

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fc_mem_O {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (x : A.Mset w0 s De) (i : ι)
    (hxi : (x : Y) ∈ (A.chart i).source) :
    A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by sorry
