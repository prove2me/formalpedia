-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_c4p__comm_aa47ceadadb7
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_c4p__comm_aa47ceadadb7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:46.864516+00:00
-- url     : https://prove2.me/theorems/ae675ceb-3aa0-5805-ae5a-34e09956a9c5
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out Cube Pf c4p  comm aa47ceadadb7: P2 M Reciprocity Theory Chart Restriction G Out Cube Pf c4p  comm aa47ceadadb7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out Cube Pf c4p  comm aa47ceadadb7 construction uses the P2 M Reciprocity Theory Chart Restriction G Out Cube Pf c4p  comm aa47ceadadb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L230-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L230-L236

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_c4p__comm_aa47ceadadb7 (a b c d : Fin 4) :
    (lift (x4 G' a) (lift (padd G' (x4 G' b) (x4 G' c)) (x4 G' d))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (x4 G a) (lift (padd G (x4 G b) (x4 G c)) (x4 G d))).left := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«CubePf».«c4p'_comm» := P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_c4p__comm_aa47ceadadb7
