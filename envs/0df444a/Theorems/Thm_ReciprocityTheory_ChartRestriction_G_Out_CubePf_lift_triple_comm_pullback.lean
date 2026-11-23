-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_lift_triple_comm_pullback
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.lift_triple_comm_pullback
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:58.166389+00:00
-- url     : https://prove2.me/theorems/51e094bf-2be6-4d30-a1d3-3427cd2ba078
-- title:
--   Cube Pf: lift triple comm pullback
-- statement:
--   The Cube Pf construction uses the lift triple comm pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L155-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L155-L161

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

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.lift_triple_comm_pullback {T : Over S'} {T0 : Over S} (L : (Over.map m.e).obj T ⟶ T0) (p q r : T ⟶ G')
    (p0 q0 r0 : T0 ⟶ G) (hp : tb m p = L ≫ p0) (hq : tb m q = L ≫ q0) (hr : tb m r = L ≫ r0) :
    (lift p (lift q r)).left ≫ m.F3 = L.left ≫ (lift p0 (lift q0 r0)).left := by sorry
