-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_specialFibre_dim_ge
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.specialFibre_dim_ge
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:56.330075+00:00
-- url     : https://prove2.me/theorems/b64d000d-db6e-4fa3-af1f-d8e7acbb5178
-- title:
--   Dim F: special Fibre dim ge
-- statement:
--   The Dim F construction uses the special Fibre dim ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L230-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L230-L264

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.specialFibre_dim_ge {σ : Type*} [Finite σ] (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap MvPolynomial.C = ⊥) (ℓ : ℤ) (hℓ : Prime ℓ)
    (q : Ideal (MvPolynomial σ ℤ ⧸ P))
    (hq : q ∈ (Ideal.span {((ℓ : ℤ) : MvPolynomial σ ℤ ⧸ P)}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ P) ≤ ringKrullDim ((MvPolynomial σ ℤ ⧸ P) ⧸ q) + 1 := by sorry
