-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_norm_periodic_const_range
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:37.254739+00:00
-- url     : https://prove2.me/theorems/e2269d68-40af-5eea-b21a-7b69bf434cf3
-- title:
--   Pullback Sections: norm periodic const range
-- statement:
--   The Pullback Sections construction uses the norm periodic const range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnFrameA.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnFrameA.lean#L58-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnFrameA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range {La : Type} [AddCommGroup La] (P : La →+ (Fin N → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (f : (Fin N → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z a, ‖f (z + P a)‖ = ‖f z‖) (z w : Fin N → ℂ) : f z = f w := by sorry
