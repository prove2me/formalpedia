-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_padd__f5517b89e58c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_padd__f5517b89e58c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:45:57.531875+00:00
-- url     : https://prove2.me/theorems/18fdc2bd-1e4b-4377-86f8-9a4923e9fae4
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out Cube Pf comp padd  f5517b89e58c: P2 M Reciprocity Theory Chart Restriction G Out Cube Pf comp padd  f5517b89e58c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out Cube Pf comp padd  f5517b89e58c construction uses the P2 M Reciprocity Theory Chart Restriction G Out Cube Pf comp padd  f5517b89e58c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeMapOfThirdFaceEqPushPtLift.lean#L99-L104

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_padd__f5517b89e58c {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] {T T' : Over S₀} (L : T' ⟶ T)
    (a b : T ⟶ H) : L ≫ padd H a b = padd H (L ≫ a) (L ≫ b) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«CubePf».«comp_padd'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_comp_padd__f5517b89e58c
