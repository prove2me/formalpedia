-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_comp
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:05.608901+00:00
-- url     : https://prove2.me/theorems/c1d2b88c-4ee0-4943-aebb-6e7b1f71313c
-- title:
--   Pullback Sections: jet Pt comp
-- statement:
--   The Pullback Sections construction uses the jet Pt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetC.lean#L34-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetC.lean#L34-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
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
variable {g : ℕ} {Y Y' : Scheme.{0}}
set_option backward.isDefEq.respectTransparency false

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_comp (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (φ : Y ⟶ Y')
    (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y')) (hol' : IsHolFam e') (he : ∀ z, e z ≫ φ = e' z) (m : ℕ) :
    jetPt e hol m ≫ φ = jetPt e' hol' m := by sorry
