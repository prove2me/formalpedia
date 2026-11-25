-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LBVal_corr_val
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LBVal.corr_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:27.838959+00:00
-- url     : https://prove2.me/theorems/dbccbf9c-443b-48ba-82c7-d00f202a3e61
-- title:
--   LBVal: corr val
-- statement:
--   The LBVal construction uses the corr val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean#L51-L60

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LBVal.corr_val (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') (j : K → L.ι) (j' : K' → L.ι) (c1 : LB.Coh L φ j)
    (c2 : LB.Coh L φ' j') (c3 : ∀ k k', φ k = φ' k' → j k = j' k') (W : Y.Opens)
    (hW : W ≤ LB.wchart L φ j ⊓ LB.wchart L φ' j') :
    (Y.presheaf.map (homOfLE (hW.trans inf_le_left)).op).hom (t.s j).val =
      (Y.presheaf.map (homOfLE (hW.trans inf_le_right)).op).hom (t'.s j').val := by sorry
