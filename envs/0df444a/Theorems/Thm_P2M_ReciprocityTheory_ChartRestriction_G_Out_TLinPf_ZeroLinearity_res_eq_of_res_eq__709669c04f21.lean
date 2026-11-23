-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_res_eq_of_res_eq__709669c04f21
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_res_eq_of_res_eq__709669c04f21
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:08.774914+00:00
-- url     : https://prove2.me/theorems/326ad68d-495e-48ee-a8e3-d52facf565f3
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity res eq of res eq  709669c04f21: P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity res eq of res eq  709669c0
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity res eq of res eq  709669c04f21 construction uses the P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity res eq of res eq  709669c04f21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L34-L47

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_res_eq_of_res_eq__709669c04f21 {U V W : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ) (h1 : W ≤ U) (h2 : W ≤ V)
    (h : res (inf_le_left : U ⊓ V ≤ U) a = res (inf_le_right : U ⊓ V ≤ V) b) :
    res h1 a = res h2 b := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«TLinPf».«ZeroLinearity».«res_eq_of_res_eq'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_res_eq_of_res_eq__709669c04f21
