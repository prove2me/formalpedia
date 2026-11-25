-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isSmoothSection_localizedSection
-- name    : ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.isSmoothSection_localizedSection
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:37:12.833743+00:00
-- url     : https://prove2.me/theorems/643d1793-131e-4bd4-9701-38586f4ad1e6
-- title:
--   Weighted Atlas: is Smooth Section localized Section
-- statement:
--   The Weighted Atlas construction uses the is Smooth Section localized Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxD.lean#L71-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxD.lean#L71-L103

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.isSmoothSection_localizedSection (la' : La) (Sf : Finset Y) (idx : Y → ι) (χ : Y → Y → ℝ) (c : Y → ℂ)
    (K : Y → Set Y) (hχ : ∀ P ∈ Sf, A.SmoothFn (χ P)) (hχs : ∀ P ∈ Sf, ∀ y, χ P y ≠ 0 → y ∈ K P)
    (hKc : ∀ P ∈ Sf, IsCompact (K P)) (hKs : ∀ P ∈ Sf, K P ⊆ (A.chart (idx P)).source) :
    A.IsSSec la' (A.F0 la' Sf idx χ c) := by sorry
