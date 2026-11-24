-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_mem_minimalPrimes
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:35.493797+00:00
-- url     : https://prove2.me/theorems/1c7fdc15-8afd-4414-b2ea-31c9d1a142d0
-- title:
--   I1: cyc is Homogeneous of mem minimal Primes
-- statement:
--   The I1 construction uses the cyc is Homogeneous of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CycDim.lean#L44-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes {A : Type*} [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] {I W : Ideal A} (hI : I.IsHomogeneous 𝒜)
    (hW : W ∈ I.minimalPrimes) : W.IsHomogeneous 𝒜 := by sorry
