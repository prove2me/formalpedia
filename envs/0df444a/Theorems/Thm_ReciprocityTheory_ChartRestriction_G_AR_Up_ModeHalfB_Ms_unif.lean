-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ms_unif
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_unif
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:46:26.652644+00:00
-- url     : https://prove2.me/theorems/1d08c97a-1509-4c3c-8c48-8304ac0fb24d
-- title:
--   Mode Half B: Ms unif
-- statement:
--   The Mode Half B construction uses the Ms unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L176-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean#L176-L240

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_unif (X : Data E r) (τ : X.Ψ) {κ : ℝ} (hκ : 1 < κ) :
    ∀ᶠ N in 𝓝 (Nid r), ∀ v : Fin r → ℂ, κ⁻¹ * ∑ k, ‖v k‖ ^ 2 ≤ Ms X.p0 X.p0_le N v ∧
      Ms X.p0 X.p0_le N v ≤ κ * ∑ k, ‖v k‖ ^ 2 := by sorry
