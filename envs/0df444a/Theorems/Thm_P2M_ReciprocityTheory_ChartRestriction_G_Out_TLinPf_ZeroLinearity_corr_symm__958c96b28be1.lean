-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_corr_symm__958c96b28be1
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_corr_symm__958c96b28be1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:17:48.401034+00:00
-- url     : https://prove2.me/theorems/d9b4faee-ebf5-45da-9d2e-f80f2904962e
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity corr symm  958c96b28be1: P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity corr symm  958c96b28be1
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity corr symm  958c96b28be1 construction uses the P2 M Reciprocity Theory Chart Restriction G Out TLin Pf Zero Linearity corr symm  958c96b28be1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L49-L54

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_corr_symm__958c96b28be1 {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') : LB.Gen.Corr L φ' ε' φ ε t' t := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«TLinPf».«ZeroLinearity».«corr_symm'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_corr_symm__958c96b28be1
