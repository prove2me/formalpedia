-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LBVal_rres
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LBVal.rres
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:43.916864+00:00
-- url     : https://prove2.me/theorems/8f6eee82-4faa-41ff-a779-efef52c3a114
-- title:
--   LBVal: rres
-- statement:
--   The LBVal construction uses the rres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean#L15-L20

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LBVal.rres {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by sorry
