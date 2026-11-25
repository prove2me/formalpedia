-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_exists_compact_reps
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_compact_reps
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:36.673492+00:00
-- url     : https://prove2.me/theorems/16928fe0-cbfd-4d96-b989-3ef16d9d44c1
-- title:
--   Pullback Sections: exists compact reps
-- statement:
--   The Pullback Sections construction uses the exists compact reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnFrameA.lean#L28-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnFrameA.lean#L28-L56

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_compact_reps {La : Type} [AddCommGroup La] (P : La →+ (Fin N → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    ∃ K : Set (Fin N → ℂ), IsCompact K ∧ ∀ z, ∃ w ∈ K, z - w ∈ P.range := by sorry
