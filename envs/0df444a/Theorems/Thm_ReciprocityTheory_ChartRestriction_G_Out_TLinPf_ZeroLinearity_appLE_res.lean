-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_appLE_res
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.appLE_res
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:25.640602+00:00
-- url     : https://prove2.me/theorems/e8bc7777-cc89-4db2-b7c1-73e7fa409d7f
-- title:
--   Zero Linearity: app LE res
-- statement:
--   The Zero Linearity construction uses the app LE res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L123-L128

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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.appLE_res (f : Z ⟶ Y) {U V : Y.Opens} (hUV : V ≤ U) {W' : Z.Opens} (hW : W' ≤ f ⁻¹ᵁ V)
    (x : Γ(Y, U)ˣ) :
    (f.appLE V W' hW).hom (res hUV x).val =
      (f.appLE U W' (hW.trans (f.preimage_mono hUV))).hom x.val := by sorry
