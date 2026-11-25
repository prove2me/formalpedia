-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_integrable_tsum_of_summable
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.integrable_tsum_of_summable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:37.979871+00:00
-- url     : https://prove2.me/theorems/7b38adeb-186e-4f44-8f6d-bafd94f20f57
-- title:
--   Geo: integrable tsum of summable
-- statement:
--   The Geo construction uses the integrable tsum of summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L117-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L117-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.integrable_tsum_of_summable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (hF : ∀ n, Integrable (F n) μ) (hs : Summable fun n => ∫ y, ‖F n y‖ ∂μ) :
    Integrable (fun y => ∑' n, F n y) μ := by sorry
