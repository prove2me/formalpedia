-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_ext_cut
-- name    : ReciprocityTheory.L2DbarEstimates.C.ext_cut
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:13.321555+00:00
-- url     : https://prove2.me/theorems/104ecb88-9a5b-4da1-932a-9425ff376a35
-- title:
--   C: ext cut
-- statement:
--   The C construction uses the ext cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCut.lean#L57-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCut.lean#L57-L219

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
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
open scoped ENNReal Manifold

theorem ReciprocityTheory.L2DbarEstimates.C.ext_cut {n : ℕ} {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {K : Set (V n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ k : ℝ, 1 ≤ k →
      ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k},
        ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 ≤ C * ENNReal.ofReal (k ^ 2) := by sorry
