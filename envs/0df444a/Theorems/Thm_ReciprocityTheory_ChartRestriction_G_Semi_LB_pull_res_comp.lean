-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_res_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_res_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:56.540126+00:00
-- url     : https://prove2.me/theorems/3cab98a7-db2d-44c2-949c-27ef52dec9e4
-- title:
--   LB: pull res comp
-- statement:
--   The LB construction uses the pull res comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L237-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L237-L241

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_res_comp (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (hV : V ≤ f ⁻¹ᵁ U)
    {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ V) (hW' : W ≤ (h ≫ f) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res hW (pullU h V (res hV (pullU f U x))) = res hW' (pullU (h ≫ f) U x) := by sorry
