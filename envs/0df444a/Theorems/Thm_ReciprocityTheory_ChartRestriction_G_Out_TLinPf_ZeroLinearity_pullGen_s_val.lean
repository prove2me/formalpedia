-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_pullGen_s_val
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.pullGen_s_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:33.804799+00:00
-- url     : https://prove2.me/theorems/2dbb931f-aaa5-4538-82c4-cdee0f9c1202
-- title:
--   Zero Linearity: pull Gen s val
-- statement:
--   The Zero Linearity construction uses the pull Gen s val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L27-L32

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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.pullGen_s_val {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) :
    ((LB.pullGen L φ ε c h).s j).val =
      (h.appLE (LB.wchart L φ j) (LB.wchart L (fun k => h ≫ φ k) j)
        (LBVal.wchart_pull_le L φ h j)).hom (c.s j).val := by sorry
