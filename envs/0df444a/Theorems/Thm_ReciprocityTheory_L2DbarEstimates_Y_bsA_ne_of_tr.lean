-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ne_of_tr
-- name    : ReciprocityTheory.L2DbarEstimates.Y.bsA_ne_of_tr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:18:19.950639+00:00
-- url     : https://prove2.me/theorems/140780bd-e083-58d5-b640-ad485d00de7b
-- title:
--   Y: bs A ne of tr
-- statement:
--   The Y construction uses the bs A ne of tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepA.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/BStepA.lean#L84-L89

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
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
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.bsA_ne_of_tr {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i j : ι}
    {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source)
    (h : a j y ≠ 0) : a i y ≠ 0 := by sorry
