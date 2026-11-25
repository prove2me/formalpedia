-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_constantCoeff_of_mem_orig
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.constantCoeff_of_mem_orig
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:15:30.381175+00:00
-- url     : https://prove2.me/theorems/6cadb4d4-c396-459e-ab92-6ad318a3504f
-- title:
--   Pullback Sections: constant Coeff of mem orig
-- statement:
--   The Pullback Sections construction uses the constant Coeff of mem orig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean#L25-L30

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.constantCoeff_of_mem_orig {p : MvPolynomial ι K} (hp : p ∈ orig K ι) : MvPolynomial.constantCoeff p = 0 := by sorry
