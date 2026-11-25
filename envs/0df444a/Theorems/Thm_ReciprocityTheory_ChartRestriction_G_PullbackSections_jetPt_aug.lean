-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_aug
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_aug
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:39:57.015518+00:00
-- url     : https://prove2.me/theorems/f4b60ab6-3540-585b-a071-fa4c3a71f0dd
-- title:
--   Pullback Sections: jet Pt aug
-- statement:
--   The Pullback Sections construction uses the jet Pt aug property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetC.lean#L58-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetC.lean#L58-L88

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_aug (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ) :
    spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) ≫ jetPt e hol m = e 0 := by sorry
