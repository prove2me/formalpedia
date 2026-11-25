-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_liouville
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_liouville
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:31.744618+00:00
-- url     : https://prove2.me/theorems/10d6a2cd-1777-463d-8e95-dc89e4758c2b
-- title:
--   Pullback Sections: vtf liouville
-- statement:
--   The Pullback Sections construction uses the vtf liouville property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean#L96-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean#L96-L128

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_liouville (lat : AddSubgroup (Fin g → ℂ)) (hspan : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤)
    (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (hper : ∀ z, ∀ a ∈ lat, ‖f (z + a)‖ = ‖f z‖)
    (z w : Fin g → ℂ) : f z = f w := by sorry
