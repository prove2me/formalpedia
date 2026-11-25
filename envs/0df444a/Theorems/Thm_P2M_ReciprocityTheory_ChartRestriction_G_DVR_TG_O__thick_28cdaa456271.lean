-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_O__thick_28cdaa456271
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_O__thick_28cdaa456271
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:15:05.95752+00:00
-- url     : https://prove2.me/theorems/e22a1b57-427c-5642-b01c-87cfa0f19d90
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR TG O  thick 28cdaa456271: P2 M Reciprocity Theory Chart Restriction G DVR TG O  thick 28cdaa456271
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR TG O  thick 28cdaa456271 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR TG O  thick 28cdaa456271 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenLevel.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenLevel.lean#L78-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenLevel
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_O__thick_28cdaa456271 (U : UnifPre I D A G) (e : ℕ) (α : D.toPre.X) (k : Fin 4) :
    thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α k = D.toPre.Oφ (U.gt e).pG α k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«TG».«Oφ_thick» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_O__thick_28cdaa456271
