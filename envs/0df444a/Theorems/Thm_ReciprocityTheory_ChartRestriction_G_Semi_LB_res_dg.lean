-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_dg
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.res_dg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:56.292144+00:00
-- url     : https://prove2.me/theorems/0e95a82c-1ca3-4059-b7ba-f131ac55d2a1
-- title:
--   LB: res dg
-- statement:
--   The LB construction uses the res dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L92-L99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open ReciprocityTheory.ChartRestriction.G.Semi.LB
variable {X Y Z : Scheme.{u}}

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.res_dg (M L : LB X) (p q : M.ι × L.ι) {W : X.Opens}
    (hW : W ≤ M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2)) :
    res hW (dg M L p q) =
      res (hW.trans (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)))
        (M.g p.1 q.1) *
      (res (hW.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
        (L.g p.2 q.2))⁻¹ := by sorry
