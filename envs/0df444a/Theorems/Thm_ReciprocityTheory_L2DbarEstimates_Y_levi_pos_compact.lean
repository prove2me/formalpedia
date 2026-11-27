-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_levi_pos_compact
-- name    : ReciprocityTheory.L2DbarEstimates.Y.levi_pos_compact
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:48.163107+00:00
-- url     : https://prove2.me/theorems/372eba0f-428c-4e7c-a189-59f191078c8d
-- title:
--   Y: levi pos compact
-- statement:
--   The Y construction uses the levi pos compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxE.lean#L48-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxE.lean#L48-L87

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE
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
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.levi_pos_compact {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) {K0 : Set (V n)} (hK0 : IsCompact K0) (hK0U : K0 ⊆ U)
    (hpos : ∀ u ∈ K0, ∀ ζ : V n, ζ ≠ 0 → 0 < (leviV n g u ζ.ofLp).re) :
    ∃ m > 0, ∀ u ∈ K0, ∀ ζ : V n, m * ‖ζ‖ ^ 2 ≤ (leviV n g u ζ.ofLp).re := by sorry
