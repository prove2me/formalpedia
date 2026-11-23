-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_gs_gF_comp
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.gs_gF_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:19.755643+00:00
-- url     : https://prove2.me/theorems/280b8bda-fad1-46c3-993a-7fe197bdb9aa
-- title:
--   Section Scalar Valuation: gs g F comp
-- statement:
--   The Section Scalar Valuation construction uses the gs g F comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/SectionScalarValuation.lean#L124-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/SectionScalarValuation.lean#L124-L135

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.gs_gF_comp {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hf : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    (y : (DegPre.BF D.toPre F).left) (ζ : F) :
    gs h y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) := by sorry
