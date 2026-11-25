-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isHomogeneous_of_mem_minimalPrimes
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isHomogeneous_of_mem_minimalPrimes
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:32.337067+00:00
-- url     : https://prove2.me/theorems/9d372454-98cc-476f-9655-9b45694f1595
-- title:
--   Geo: is Homogeneous of mem minimal Primes
-- statement:
--   The Geo construction uses the is Homogeneous of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean#L78-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem ReciprocityTheory.ChartRestriction.G.Geo.isHomogeneous_of_mem_minimalPrimes {A : Type*} [CommRing A] (𝒜 : ℕ → Submodule ℤ A)
    [GradedRing 𝒜] {I W : Ideal A} (hI : I.IsHomogeneous 𝒜) (hW : W ∈ I.minimalPrimes) :
    W.IsHomogeneous 𝒜 := by sorry
