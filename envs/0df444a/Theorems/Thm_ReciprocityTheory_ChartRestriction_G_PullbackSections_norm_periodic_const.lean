-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_norm_periodic_const
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:45.251653+00:00
-- url     : https://prove2.me/theorems/3f3fd373-7cc0-5899-a0de-4688e9654788
-- title:
--   Pullback Sections: norm periodic const
-- statement:
--   The Pullback Sections construction uses the norm periodic const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnFrameA.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnFrameA.lean#L13-L26

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const (f : (Fin N → ℂ) → ℂ) (hf : Differentiable ℂ f) (L : AddSubgroup (Fin N → ℂ))
    (K : Set (Fin N → ℂ)) (hK : IsCompact K) (hcov : ∀ z, ∃ w ∈ K, z - w ∈ L)
    (hper : ∀ z, ∀ l ∈ L, ‖f (z + l)‖ = ‖f z‖) (z w : Fin N → ℂ) : f z = f w := by sorry
