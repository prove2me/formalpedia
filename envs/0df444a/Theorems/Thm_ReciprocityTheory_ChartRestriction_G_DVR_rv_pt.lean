-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rv_pt
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.rv_pt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:03.416262+00:00
-- url     : https://prove2.me/theorems/6c8666b5-3d9c-4f49-9960-eab8228564c2
-- title:
--   DVR: rv pt
-- statement:
--   The DVR construction uses the rv pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RValuePf.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RValuePf.lean#L27-L34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValuePf
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem ReciprocityTheory.ChartRestriction.G.DVR.rv_pt (x y : D.toPre.X) :
    (lift (toUnit (TF (R := V) F) ≫ D.toPre.c x) (toUnit (TF (R := V) F) ≫ D.toPre.c y) :
      TF (R := V) F ⟶ D.toPre.P.A ⊗ D.toPre.P.A).left = jFK (R := V) F ≫ D.toPre.pt2 x y := by sorry
