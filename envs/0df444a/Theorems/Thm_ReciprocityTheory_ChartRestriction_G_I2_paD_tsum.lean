-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paD_tsum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paD_tsum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:54.545694+00:00
-- url     : https://prove2.me/theorems/b18fcd41-e576-42d6-8f58-9ff8a5e60baa
-- title:
--   I2: pa D tsum
-- statement:
--   The I2 construction uses the pa D tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L233-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L233-L241

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.paD_tsum {κ : Type} (G : κ → EuclideanSpace ℂ ι → ℂ) (hG : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (G k))
    (hb : ∀ R : ℝ, ∃ u : κ → ℝ, Summable u ∧ ∀ k v, ‖v‖ ≤ R → ‖G k v‖ ≤ u k) :
    Differentiable ℂ (fun v => ∑' k, G k v) ∧
      ∀ α : ι →₀ ℕ, HasSum (fun k => paD α (G k)) (paD α (fun v => ∑' k, G k v)) := by sorry
