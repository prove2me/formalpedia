-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_s_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_s_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:37.547808+00:00
-- url     : https://prove2.me/theorems/5dde4a94-e332-4c56-8239-d6b511fd0cf0
-- title:
--   Weighted Atlas: sqn s eq
-- statement:
--   The Weighted Atlas construction uses the sqn s eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZLocLower.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/ZLocLower.lean#L62-L72

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
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
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_s_eq (A : WeightedAtlas n Y ι La) {L : La} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) {i : ι} {x : Y} (hx : x ∈ (A.chart i).source)
    (hw : w0 i x ≠ 0) :
    A.sqn L s x = ‖w0 i x‖ ^ 2 * Real.exp (-A.ph L i x) * ‖A.zLoc w0 s i (A.chart i x)‖ ^ 2 := by sorry
