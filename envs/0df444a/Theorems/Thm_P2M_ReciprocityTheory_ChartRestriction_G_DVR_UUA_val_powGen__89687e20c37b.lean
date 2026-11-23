-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_val_powGen__89687e20c37b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_val_powGen__89687e20c37b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:39.523938+00:00
-- url     : https://prove2.me/theorems/71909c33-7dfe-488c-b20c-9d029380a4d7
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR UUA val pow Gen  89687e20c37b: P2 M Reciprocity Theory Chart Restriction G DVR UUA val pow Gen  89687e20c37b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR UUA val pow Gen  89687e20c37b construction uses the P2 M Reciprocity Theory Chart Restriction G DVR UUA val pow Gen  89687e20c37b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValPowGen.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValPowGen.lean#L54-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CubicNormMulIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_val_powGen__89687e20c37b {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«UUA».«val_powGen'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_val_powGen__89687e20c37b
