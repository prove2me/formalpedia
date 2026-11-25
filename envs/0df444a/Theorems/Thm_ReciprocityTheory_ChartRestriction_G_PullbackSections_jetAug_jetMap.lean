-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_jetMap
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_jetMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:07:45.233958+00:00
-- url     : https://prove2.me/theorems/6c9ecd8c-cb5f-5dcf-b090-5c8f7b354391
-- title:
--   Pullback Sections: jet Aug jet Map
-- statement:
--   The Pullback Sections construction uses the jet Aug jet Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L62-L76

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_jetMap {ι' : Type} (φ : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι') (a : Jet K ι m) :
    (jetAug : Jet K ι' m →ₐ[K] K) (jetMap φ hφ a) = (jetAug : Jet K ι m →ₐ[K] K) a := by sorry
