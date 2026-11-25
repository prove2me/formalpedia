-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_res_appTop
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.res_appTop
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:20.717267+00:00
-- url     : https://prove2.me/theorems/ba4fcb00-e0f3-5243-b81c-1ba10b9f37b6
-- title:
--   TLin Pf: res app Top
-- statement:
--   The TLin Pf construction uses the res app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/CompBaseEq.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/CompBaseEq.lean#L25-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ActActA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_CompBaseEq
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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.res_appTop {A B : Scheme.{0}} (f : A ⟶ B) {W : A.Opens} (hW : W ≤ f ⁻¹ᵁ ⊤) (x : Γ(B, ⊤)) :
    (A.presheaf.map (homOfLE hW).op).hom (f.appTop.hom x) = (f.appLE ⊤ W hW).hom x := by sorry
