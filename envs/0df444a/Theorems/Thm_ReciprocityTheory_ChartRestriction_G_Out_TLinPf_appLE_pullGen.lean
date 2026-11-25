-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_appLE_pullGen
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.appLE_pullGen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:28.956813+00:00
-- url     : https://prove2.me/theorems/c9d51fe6-fd4a-5837-8d06-edd75d6f8b48
-- title:
--   TLin Pf: app LE pull Gen
-- statement:
--   The TLin Pf construction uses the app LE pull Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/WchartInlLe.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/WchartInlLe.lean#L44-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
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
variable {Y Z : Scheme.{0}} (L : LB Y) {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.appLE_pullGen {T X : Scheme.{0}} (f : T ⟶ Z) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (L : LB X)
    (c : LB.Gen (LB.LinComb L φ ε)) (hh : Z ⟶ Y) (j : K → L.ι) (W' : T.Opens)
    (h : W' ≤ f ⁻¹ᵁ LB.wchart L (fun k => hh ≫ φ k) j) :
    (f.appLE _ W' h).hom ((LB.pullGen L φ ε c hh).s j).val =
      ((f ≫ hh).appLE (LB.wchart L φ j) W'
        (fun _ hz => Semi.LBVal.wchart_pull_le L φ hh j (h hz))).hom (c.s j).val := by sorry
