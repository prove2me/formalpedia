-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_cocycle
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_cocycle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:19.358912+00:00
-- url     : https://prove2.me/theorems/c6b1532b-02ca-424b-970b-0705837155fd
-- title:
--   LB: pull cocycle
-- statement:
--   The LB construction uses the pull cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L59-L70

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_cocycle {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i j k : L.ι) {W : Y.Opens}
    (h₁ : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j)) (h₂ : W ≤ f ⁻¹ᵁ (L.U j ⊓ L.U k))
    (h₃ : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    res h₁ (pullU f _ (L.g i j)) * res h₂ (pullU f _ (L.g j k)) =
      res h₃ (pullU f _ (L.g i k)) := by sorry
