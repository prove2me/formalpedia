-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LBVal_mulGen_val
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LBVal.mulGen_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:46.30863+00:00
-- url     : https://prove2.me/theorems/cbf9bafe-25bf-4c99-a2dc-ffe476c29270
-- title:
--   LBVal: mul Gen val
-- statement:
--   The LBVal construction uses the mul Gen val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean#L33-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
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
  CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LBVal
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.Semi.LBVal.mulGen_val (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι)
    (W : Y.Opens) (hW : W ≤ LB.wchart L (Sum.elim φ φ') j) :
    (Y.presheaf.map (homOfLE hW).op).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      (Y.presheaf.map (homOfLE (hW.trans (fun _ hy => Set.mem_iInter.2 fun k =>
          Set.mem_iInter.1 hy (Sum.inl k)))).op).hom (t.s (j ∘ Sum.inl)).val *
      (Y.presheaf.map (homOfLE (hW.trans (fun _ hy => Set.mem_iInter.2 fun k =>
          Set.mem_iInter.1 hy (Sum.inr k)))).op).hom (t'.s (j ∘ Sum.inr)).val := by sorry
