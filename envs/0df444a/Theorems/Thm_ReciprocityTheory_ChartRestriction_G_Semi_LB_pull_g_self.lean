-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_g_self
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_g_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:22.605213+00:00
-- url     : https://prove2.me/theorems/8edfc8ab-4e6f-40a9-b62e-7b65f57e3292
-- title:
--   LB: pull g self
-- statement:
--   The LB construction uses the pull g self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L55-L57

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_g_self {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι) {W : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U i)) : res h (pullU f _ (L.g i i)) = 1 := by sorry
