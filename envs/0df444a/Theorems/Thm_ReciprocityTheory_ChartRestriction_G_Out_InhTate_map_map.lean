-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_InhTate_map_map
-- name    : ReciprocityTheory.ChartRestriction.G.Out.InhTate.map_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:44.408391+00:00
-- url     : https://prove2.me/theorems/e461e12a-205d-4bb4-9b33-5cf0fc9b0e63
-- title:
--   Inh Tate: map map
-- statement:
--   The Inh Tate construction uses the map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/InhTate.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/InhTate.lean#L64-L67

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

theorem ReciprocityTheory.ChartRestriction.G.Out.InhTate.map_map {Y : Scheme.{0}} {U V W : Y.Opens} (h : W ≤ V) (h' : V ≤ U) (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((Y.presheaf.map (homOfLE h').op).hom y) =
      (Y.presheaf.map (homOfLE (h.trans h')).op).hom y := by sorry
