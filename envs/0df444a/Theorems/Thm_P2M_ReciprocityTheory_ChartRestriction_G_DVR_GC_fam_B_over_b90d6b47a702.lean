-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam_B_over_b90d6b47a702
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam_B_over_b90d6b47a702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:51.148151+00:00
-- url     : https://prove2.me/theorems/65f8d2f0-bbba-4719-9438-20fb6d19a777
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR GC fam B over b90d6b47a702: P2 M Reciprocity Theory Chart Restriction G DVR GC fam B over b90d6b47a702
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR GC fam B over b90d6b47a702 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR GC fam B over b90d6b47a702 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L238-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L238-L240

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
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam_B_over_b90d6b47a702 (α : D.toPre.X) (k : Fin 4) :
    D.toPre.famφB α k ≫ D.toPre.P.A.hom = D.toPre.P.A.hom := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«GC».«famφB_over» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam_B_over_b90d6b47a702
