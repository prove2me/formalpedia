-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_pullU_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.LB.res_pullU_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:58.493572+00:00
-- url     : https://prove2.me/theorems/9674a265-9f33-43b6-a89c-9e3b320215b9
-- title:
--   LB: res pull U eq
-- statement:
--   The LB construction uses the res pull U eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsbLb.lean#L34-L37

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.LB.res_pullU_eq (f : Y ⟶ X) {U U' : X.Opens} (hU' : U' ≤ U) {W : Y.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) (hW' : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) :
    res hW (pullU f U x) = res hW' (pullU f U' (res hU' x)) := by sorry
