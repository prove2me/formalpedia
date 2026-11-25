-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_pzero__f3738fc98f21
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_pzero__f3738fc98f21
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:37.497921+00:00
-- url     : https://prove2.me/theorems/3df3a19c-bbbd-48ff-a8f6-a1839b6035bf
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out Cube Pf tb pzero  f3738fc98f21: P2 M Reciprocity Theory Chart Restriction G Out Cube Pf tb pzero  f3738fc98f21
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out Cube Pf tb pzero  f3738fc98f21 construction uses the P2 M Reciprocity Theory Chart Restriction G Out Cube Pf tb pzero  f3738fc98f21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L181-L183

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_pzero__f3738fc98f21 {T : Over S'} {T0 : Over S} (L : (Over.map m.e).obj T ⟶ T0) :
    tb m (pzero G' T) = L ≫ pzero G T0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«CubePf».«tb_pzero'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_pzero__f3738fc98f21
