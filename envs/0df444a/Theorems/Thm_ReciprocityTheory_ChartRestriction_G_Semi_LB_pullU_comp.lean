-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.pullU_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:03.034577+00:00
-- url     : https://prove2.me/theorems/5e03176f-99b4-404f-9006-cd9fa569c725
-- title:
--   LB: pull U comp
-- statement:
--   The LB construction uses the pull U comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L233-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L233-L235

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.pullU_comp (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (h ≫ f) U x = pullU h (f ⁻¹ᵁ U) (pullU f U x) := by sorry
