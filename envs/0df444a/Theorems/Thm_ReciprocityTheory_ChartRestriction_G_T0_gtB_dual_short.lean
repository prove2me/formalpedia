-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtB_dual_short
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gtB_dual_short
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:52.561293+00:00
-- url     : https://prove2.me/theorems/de81abdc-7fe3-449a-a0be-2364ed76b307
-- title:
--   T0: gt B dual short
-- statement:
--   The T0 construction uses the gt B dual short property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L87-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L87-L146

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule

theorem ReciprocityTheory.ChartRestriction.G.T0.gtB_dual_short {n : ℕ} (hn : 0 < n) (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) ∧
      ‖y‖ ≤ n / lam := by sorry
