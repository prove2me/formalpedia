-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_appLE_one
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.appLE_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:53.860137+00:00
-- url     : https://prove2.me/theorems/fe18ed57-4cd2-51e2-928c-689febac86ab
-- title:
--   Zero Linearity: app LE one
-- statement:
--   The Zero Linearity construction uses the app LE one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L113-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L113-L121

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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.appLE_one {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hC : LB.Gen.Corr L _ ε PEmpty.elim PEmpty.elim (LB.pullGen L φ ε t h) (LB.oneGen L))
    (j : K → L.ι) (hj : LB.Coh L (fun k => h ≫ φ k) j) (V : Z.Opens)
    (hV : V ≤ LB.wchart L (fun k => h ≫ φ k) j) :
    (h.appLE (LB.wchart L φ j) V (hV.trans (LBVal.wchart_pull_le L φ h j))).hom (t.s j).val = 1 := by sorry
