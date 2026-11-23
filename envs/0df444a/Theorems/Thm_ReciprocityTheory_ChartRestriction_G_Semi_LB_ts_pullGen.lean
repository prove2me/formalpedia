-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_ts_pullGen
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.ts_pullGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:30.375089+00:00
-- url     : https://prove2.me/theorems/2a39e536-75d5-41d7-8b9f-6026456182a2
-- title:
--   LB: ts pull Gen
-- statement:
--   The LB construction uses the ts pull Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L229-L231

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
variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.ts_pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : Gen (LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) :
    ts (pullGen L φ ε c h) j = res (wchart_comp_le L h φ j) (pullU h _ (ts c j)) := by sorry
