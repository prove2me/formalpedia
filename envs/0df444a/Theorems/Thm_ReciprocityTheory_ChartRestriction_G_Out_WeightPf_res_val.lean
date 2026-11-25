-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_res_val
-- name    : ReciprocityTheory.ChartRestriction.G.Out.WeightPf.res_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:46.829467+00:00
-- url     : https://prove2.me/theorems/06931e10-8cc2-5d68-98c9-5ccbfd91a8b5
-- title:
--   Weight Pf: res val
-- statement:
--   The Weight Pf construction uses the res val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/CancelSecAct.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/CancelSecAct.lean#L114-L115

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem ReciprocityTheory.ChartRestriction.G.Out.WeightPf.res_val {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res h u : Γ(X, V)ˣ) : Γ(X, V)) = (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := by sorry
