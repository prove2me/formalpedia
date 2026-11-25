-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_ball_cmp
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.ball_cmp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:48:54.229643+00:00
-- url     : https://prove2.me/theorems/8f2b6738-a41d-4cc8-966d-577a518c9a0b
-- title:
--   Mode Half B: ball cmp
-- statement:
--   The Mode Half B construction uses the ball cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L261-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L261-L286

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.ball_cmp (X : Data E r) {κ : ℝ} (hκ : 1 < κ) : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
    ∀ u, IsOrth X u → ∀ z : V (nd X), ‖z‖ < ρ → ∀ τ (v : Fin r → ℂ),
      κ⁻¹ * X.maj u τ v ≤ X.maj (cpt X u z) τ v ∧ X.maj (cpt X u z) τ v ≤ κ * X.maj u τ v := by sorry
