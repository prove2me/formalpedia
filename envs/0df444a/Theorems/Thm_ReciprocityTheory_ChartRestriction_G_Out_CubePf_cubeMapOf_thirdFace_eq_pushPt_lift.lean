-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_cubeMapOf_thirdFace_eq_pushPt_lift
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubeMapOf_thirdFace_eq_pushPt_lift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:49.083589+00:00
-- url     : https://prove2.me/theorems/dec5c525-21fc-4521-821d-b7f8b141fadb
-- title:
--   Cube Pf: cube Map Of third Face eq push Pt lift
-- statement:
--   The Cube Pf construction uses the cube Map Of third Face eq push Pt lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L130-L132

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

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubeMapOf_thirdFace_eq_pushPt_lift : m.F3 = (L3 m).left := by sorry
