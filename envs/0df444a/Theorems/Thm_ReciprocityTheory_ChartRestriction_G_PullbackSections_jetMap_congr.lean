-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetMap_congr
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetMap_congr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:08.353409+00:00
-- url     : https://prove2.me/theorems/008e041d-4b7f-52ba-98f5-66684f1a4d06
-- title:
--   Pullback Sections: jet Map congr
-- statement:
--   The Pullback Sections construction uses the jet Map congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L78-L89

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetMap_congr {ι' : Type} (φ φ' : ι → MvPolynomial ι' K) (hφ : ∀ i, φ i ∈ orig K ι')
    (hφ' : ∀ i, φ' i ∈ orig K ι')
    (h : ∀ i, Ideal.Quotient.mk (orig K ι' ^ (m + 1)) (φ i) = Ideal.Quotient.mk (orig K ι' ^ (m + 1)) (φ' i))
    (a : Jet K ι m) : jetMap φ hφ a = jetMap φ' hφ' a := by sorry
