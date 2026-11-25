-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_InhTate_app_res
-- name    : ReciprocityTheory.ChartRestriction.G.Out.InhTate.app_res
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:31:32.084883+00:00
-- url     : https://prove2.me/theorems/15032879-78c5-56d8-a874-5b1a6a81a3cf
-- title:
--   Inh Tate: app res
-- statement:
--   The Inh Tate construction uses the app res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/InhTate.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/InhTate.lean#L53-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
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
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.InhTate
open Semi Inh

theorem ReciprocityTheory.ChartRestriction.G.Out.InhTate.app_res {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Γ(X, ⊤)) (V : X.Opens) (W : Y.Opens)
    (h : W ≤ f ⁻¹ᵁ V) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.app V).hom ((X.presheaf.map (homOfLE le_top).op).hom y)) =
      (Y.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom y) := by sorry
