-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_dg_self
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.dg_self
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:46.379804+00:00
-- url     : https://prove2.me/theorems/556b5dca-6059-4733-8703-f4b175427314
-- title:
--   LB: dg self
-- statement:
--   The LB construction uses the dg self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L101-L104

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.dg_self {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (p : M.ι × L.ι) :
    res (le_inf le_rfl le_rfl : M.U p.1 ⊓ L.U p.2 ≤ M.U p.1 ⊓ L.U p.2 ⊓ (M.U p.1 ⊓ L.U p.2))
      (dg M L p p) = 1 := by sorry
