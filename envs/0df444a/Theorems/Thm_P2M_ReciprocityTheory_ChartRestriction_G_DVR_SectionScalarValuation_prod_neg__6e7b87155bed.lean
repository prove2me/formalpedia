-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_neg__6e7b87155bed
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_neg__6e7b87155bed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:48.320962+00:00
-- url     : https://prove2.me/theorems/5b9011b2-d6b4-49e4-92d5-97b93ccab0ac
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation prod neg  6e7b87155bed: P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation prod neg  6e7b87155bed
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation prod neg  6e7b87155bed construction uses the P2 M Reciprocity Theory Chart Restriction G DVR Section Scalar Valuation prod neg  6e7b87155bed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdNeg.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdNeg.lean#L56-L58

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_neg__6e7b87155bed {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) {c : U} (h : ∏ i, f i ^ e i = c) :
    ∏ i, f i ^ (-e i) = c⁻¹ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«SectionScalarValuation».«prod_neg'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_neg__6e7b87155bed
