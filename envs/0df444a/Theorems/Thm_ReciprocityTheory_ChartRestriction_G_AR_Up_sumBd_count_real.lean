-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_count_real
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_count_real
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:43.404526+00:00
-- url     : https://prove2.me/theorems/9fff0643-8182-5cbb-9340-10698fc551f0
-- title:
--   Up: sum Bd count real
-- statement:
--   The Up construction uses the sum Bd count real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfC.lean#L60-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfC.lean#L60-L109

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_count_real {f : ℕ} {ι : Type*} (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (hU : ∀ a k, IsUpq (x a k)) {c : ℝ} (hc : 0 < c)
    (hsep : ∀ a b, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖)
    {R : ℝ} (hR : 1 ≤ R) :
    (({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (((4 * (((p + q : ℕ) : ℝ) + 1) / c + 3) * R ^ 2) ^ (f * ((p + q) * ((p + q) * 2)))) := by sorry
