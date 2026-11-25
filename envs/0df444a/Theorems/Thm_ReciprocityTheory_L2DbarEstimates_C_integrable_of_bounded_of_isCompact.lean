-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_integrable_of_bounded_of_isCompact
-- name    : ReciprocityTheory.L2DbarEstimates.C.integrable_of_bounded_of_isCompact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:58.868578+00:00
-- url     : https://prove2.me/theorems/d78af8a8-4139-457e-9158-6c8f59348a91
-- title:
--   C: integrable of bounded of is Compact
-- statement:
--   The C construction uses the integrable of bounded of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L73-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L73-L91

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.integrable_of_bounded_of_isCompact {T : Set (V n)} (hT : IsCompact T) {h : V n → ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict T)) {C : ℝ} (hb : ∀ z ∈ T, ‖h z‖ ≤ C)
    (h0 : ∀ z ∉ T, h z = 0) : Integrable h := by sorry
