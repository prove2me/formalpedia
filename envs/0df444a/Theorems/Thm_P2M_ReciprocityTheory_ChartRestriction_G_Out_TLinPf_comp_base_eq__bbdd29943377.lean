-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_comp_base_eq__bbdd29943377
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_comp_base_eq__bbdd29943377
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:54.015398+00:00
-- url     : https://prove2.me/theorems/a5670ac3-2074-4873-aee6-f472cbd2a7ae
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out TLin Pf comp base eq  bbdd29943377: P2 M Reciprocity Theory Chart Restriction G Out TLin Pf comp base eq  bbdd29943377
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out TLin Pf comp base eq  bbdd29943377 construction uses the P2 M Reciprocity Theory Chart Restriction G Out TLin Pf comp base eq  bbdd29943377 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/CompBaseEq.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/CompBaseEq.lean#L31-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ActActA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_CompBaseEq
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_comp_base_eq__bbdd29943377 {A B C : Scheme.{0}} {a b : A ⟶ B} {ψ : B ⟶ C} (h : a ≫ ψ = b ≫ ψ) (z : A) :
    ψ (a z) = ψ (b z) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«TLinPf».«comp_base_eq'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_comp_base_eq__bbdd29943377
