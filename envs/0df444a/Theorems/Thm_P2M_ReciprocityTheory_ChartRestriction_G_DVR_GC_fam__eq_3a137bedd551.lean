-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:33:38.209181+00:00
-- url     : https://prove2.me/theorems/be505bc4-1be2-41e0-9782-e90c9cd3dedf
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR GC fam  eq 3a137bedd551: P2 M Reciprocity Theory Chart Restriction G DVR GC fam  eq 3a137bedd551
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR GC fam  eq 3a137bedd551 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR GC fam  eq 3a137bedd551 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L67-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L67-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
  [Algebra (FractionRing R) F]

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551 (α : D.X) (k : Fin 4) :
    DegPre.famφ D F α k = (DegPre.prB D F).left ≫ D.famφB α k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«GC».«famφ_eq» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
