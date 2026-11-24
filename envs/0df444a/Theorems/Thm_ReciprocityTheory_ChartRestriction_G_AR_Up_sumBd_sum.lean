-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_sum
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:26.776455+00:00
-- url     : https://prove2.me/theorems/874bc619-ce47-49fe-b6a2-5d715105dec0
-- title:
--   Up: sum Bd sum
-- statement:
--   The Up construction uses the sum Bd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfC.lean#L111-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfC.lean#L111-L205

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sum {f : ℕ} {s c : ℝ} (hs : 2 * (f : ℝ) * ((p + q : ℕ) : ℝ) ^ 2 < s) (hc : 0 < c) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ),
      (∀ a k, IsUpq (x a k)) →
      (∀ a b, a ≠ b → ∃ k i j,
        c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) →
      ∑' a, ENNReal.ofReal (∏ k, (Complex.normSq (det (x a k).toBlocks₂₂))⁻¹ ^ s) ≤ C := by sorry
