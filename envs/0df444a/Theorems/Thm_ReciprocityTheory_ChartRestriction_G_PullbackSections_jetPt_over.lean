-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_over
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_over
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:25.381196+00:00
-- url     : https://prove2.me/theorems/ac5253ee-6a09-5b49-9cf5-831073cb2b87
-- title:
--   Pullback Sections: jet Pt over
-- statement:
--   The Pullback Sections construction uses the jet Pt over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetE.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetE.lean#L58-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_over (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (p : Y ⟶ Y') (u : Sp ℂ ⟶ Y')
    (he : ∀ z, e z ≫ p = u) (m : ℕ) :
    jetPt e hol m ≫ p = spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ u := by sorry
