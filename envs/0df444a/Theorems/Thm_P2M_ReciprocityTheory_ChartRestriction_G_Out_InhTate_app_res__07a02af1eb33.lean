-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_InhTate_app_res__07a02af1eb33
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_InhTate_app_res__07a02af1eb33
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:48.751383+00:00
-- url     : https://prove2.me/theorems/51893850-1594-44ca-8545-05664da3af78
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out Inh Tate app res  07a02af1eb33: P2 M Reciprocity Theory Chart Restriction G Out Inh Tate app res  07a02af1eb33
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out Inh Tate app res  07a02af1eb33 construction uses the P2 M Reciprocity Theory Chart Restriction G Out Inh Tate app res  07a02af1eb33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/InhTate.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/InhTate.lean#L59-L62

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_InhTate_app_res__07a02af1eb33 {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Γ(X, ⊤)) (V : X.Opens) :
    (f.app V).hom ((X.presheaf.map (homOfLE le_top).op).hom y) =
      (Y.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom y) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«InhTate».«app_res'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_InhTate_app_res__07a02af1eb33
