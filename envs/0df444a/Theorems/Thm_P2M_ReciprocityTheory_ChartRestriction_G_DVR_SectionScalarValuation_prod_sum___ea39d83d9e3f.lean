-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_sum___ea39d83d9e3f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_sum___ea39d83d9e3f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:05:56.917201+00:00
-- url     : https://prove2.me/theorems/3ee3e7f6-e6f9-4f00-8bb2-e5a4f9873c27
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation prod sum   ea39d83d9e3f: P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation prod sum   ea39d83d9e3f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation prod sum   ea39d83d9e3f construction uses the P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation prod sum   ea39d83d9e3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdNeg.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdNeg.lean#L60-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_sum___ea39d83d9e3f {K K' U : Type} [Fintype K] [Fintype K'] [CommGroup U] (f : K ⊕ K' → U) {c c' : U}
    (h : ∏ i, f (.inl i) = c) (h' : ∏ i, f (.inr i) = c') : ∏ i, f i = c * c' := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«SectionScalarValuation».«prod_sum₂'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_sum___ea39d83d9e3f
