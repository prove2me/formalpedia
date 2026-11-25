-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_appLE_mulGen
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.appLE_mulGen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:27.971309+00:00
-- url     : https://prove2.me/theorems/0d0667d2-9506-4b5b-b94f-5e150154cb0c
-- title:
--   TLin Pf: app LE mul Gen
-- statement:
--   The TLin Pf construction uses the app LE mul Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/WchartInlLe.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/WchartInlLe.lean#L35-L42

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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.appLE_mulGen {T : Scheme.{0}} (f : T ⟶ Z) (φ : K → (Z ⟶ Y)) (ε : K → ℤ) (φ' : K' → (Z ⟶ Y))
    (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (j : K ⊕ K' → L.ι) (W' : T.Opens) (h : W' ≤ f ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j) :
    (f.appLE _ W' h).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      (f.appLE (LB.wchart L φ (j ∘ Sum.inl)) W' (fun _ hz => wchart_inl_le L φ φ' j (h hz))).hom (t.s (j ∘ Sum.inl)).val *
      (f.appLE (LB.wchart L φ' (j ∘ Sum.inr)) W' (fun _ hz => wchart_inr_le L φ φ' j (h hz))).hom (t'.s (j ∘ Sum.inr)).val := by sorry
