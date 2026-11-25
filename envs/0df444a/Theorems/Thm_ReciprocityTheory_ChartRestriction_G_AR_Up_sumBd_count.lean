-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_count
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_count
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:01:34.876902+00:00
-- url     : https://prove2.me/theorems/e8852050-af90-44fb-96f1-18804fd1c5f4
-- title:
--   Up: sum Bd count
-- statement:
--   The Up construction uses the sum Bd count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfB.lean#L131-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfB.lean#L131-L181

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_count {f : ℕ} {ι : Type*} (x : ι → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    {R η : ℝ} (hη : 0 < η)
    (hsep2 : ∀ a, (∀ k i j, ‖x a k i j‖ ≤ R) → ∀ b, (∀ k i j, ‖x b k i j‖ ≤ R) → a ≠ b →
      ∃ k i j, 2 * η ≤ ‖x b k i j - x a k i j‖) :
    ({a | ∀ k i j, ‖x a k i j‖ ≤ R} : Set ι).encard ≤
      ((Fintype.piFinset fun _ : Fin f × (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) × Bool =>
        Finset.Icc (-⌈R / η⌉) ⌈R / η⌉).card : ℕ∞) := by sorry
