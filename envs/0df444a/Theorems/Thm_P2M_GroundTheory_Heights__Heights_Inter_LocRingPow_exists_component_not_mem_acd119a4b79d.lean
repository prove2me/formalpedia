-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_exists_component_not_mem_acd119a4b79d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_exists_component_not_mem_acd119a4b79d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:22:49.762368+00:00
-- url     : https://prove2.me/theorems/419ebac9-8afe-4900-b117-8b4f8fe8cdd2
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Pow exists component not mem acd119a4b79d: P2 M Ground Theory Heights  Heights Inter Loc Ring Pow exists component not mem acd119a4b79d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Pow exists component not mem acd119a4b79d construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Pow exists component not mem acd119a4b79d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L53-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingPow
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_exists_component_not_mem_acd119a4b79d {J : Ideal (MRing ι)} {f : MRing ι} (hf : f ∉ J) :
    ∃ D : K → ℕ, weightedHomogeneousComponent (multiDegWeight ι) D f ∉ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingPow».«exists_component_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_exists_component_not_mem_acd119a4b79d
