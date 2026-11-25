-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBVal_charGen_val
-- name    : ReciprocityTheory.ChartRestriction.G.Out.LBVal.charGen_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:21:16.014025+00:00
-- url     : https://prove2.me/theorems/eb71d563-0479-45b3-ad9a-ee034d845748
-- title:
--   LBVal: char Gen val
-- statement:
--   The LBVal construction uses the char Gen val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean#L68-L77

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.LBVal
open Semi

theorem ReciprocityTheory.ChartRestriction.G.Out.LBVal.charGen_val {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {Z : Scheme.{0}}
    (L : LB Z) (χ : X) (j : PEmpty → L.ι) (W : (splitTorus S X ⊗ G).left.Opens)
    (hW : W ≤ LB.wchart L (Y := (splitTorus S X ⊗ G).left) (K := PEmpty) PEmpty.elim j) :
    ((splitTorus S X ⊗ G).left.presheaf.map (homOfLE hW).op).hom ((charGen X G L χ).s j).val =
      ((splitTorus S X ⊗ G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP X G χ) := by sorry
