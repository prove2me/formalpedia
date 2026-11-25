-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.isLocalHom_jetMap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:55:20.981749+00:00
-- url     : https://prove2.me/theorems/056b76fa-279f-459c-bf7d-090aec4c5d8e
-- title:
--   Pullback Sections: is Local Hom jet Map
-- statement:
--   The Pullback Sections construction uses the is Local Hom jet Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L91-L95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {K : Type} [Field K] {ι : Type} {m : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.isLocalHom_jetMap {ι' : Type} (φ : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι') :
    IsLocalHom ((jetMap (m := m) φ hφ : Jet K ι m →ₐ[K] Jet K ι' m) : Jet K ι m →+* Jet K ι' m) := by sorry
