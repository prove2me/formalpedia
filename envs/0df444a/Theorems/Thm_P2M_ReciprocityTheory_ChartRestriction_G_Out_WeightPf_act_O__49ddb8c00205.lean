-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_O__49ddb8c00205
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_O__49ddb8c00205
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:33.069037+00:00
-- url     : https://prove2.me/theorems/5cec56aa-eef7-49dc-a8ca-ccaf394d7c22
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out Weight Pf act O  49ddb8c00205: P2 M Reciprocity Theory Chart Restriction G Out Weight Pf act O  49ddb8c00205
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out Weight Pf act O  49ddb8c00205 construction uses the P2 M Reciprocity Theory Chart Restriction G Out Weight Pf act O  49ddb8c00205 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/CancelSecAct.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/CancelSecAct.lean#L79-L87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_O__49ddb8c00205 (χ : D.X) (k : Fin 4) :
    (act g).left ≫ D.Oφ g.pG χ k = (snd (Te D I e) (thickObj R I e G)).left ≫ D.Oφ g.pG χ k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«WeightPf».«act_Oφ» := P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_O__49ddb8c00205
