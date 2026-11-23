-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_map_rfl__124873d90145
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_map_rfl__124873d90145
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:12.129127+00:00
-- url     : https://prove2.me/theorems/fee9fe57-b5bf-4430-be6b-4f668e46d8ff
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity map rfl  124873d90145: P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity map rfl  124873d90145
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity map rfl  124873d90145 construction uses the P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity map rfl  124873d90145 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L23-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_map_rfl__124873d90145 {V : Y.Opens} (x : Γ(Y, V)) :
    (Y.presheaf.map (homOfLE (le_rfl : V ≤ V)).op).hom x = x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«TLinPf».«ZeroLinearity».«map_rfl'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_map_rfl__124873d90145
