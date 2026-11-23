-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_sliceGroup_67318eca5e77
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_sliceGroup_67318eca5e77
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:52.951796+00:00
-- url     : https://prove2.me/theorems/96a41c75-3bf1-44c4-87ea-37a490d9be9a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume mem slice Group 67318eca5e77: P2 M Ground Theory Heights  Heights Finite Covolume mem slice Group 67318eca5e77
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume mem slice Group 67318eca5e77 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume mem slice Group 67318eca5e77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsDoubleCoset.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsDoubleCoset.lean#L19-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] [TopologicalSpace G]
  [TopologicalSpace G₁] [TopologicalSpace G₂]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_sliceGroup_67318eca5e77 {Φ : G ≃ₜ* G₁ × G₂} {Γ : Subgroup G} {K : Subgroup G₂} {s : G₂} {x : G₁} :
    x ∈ sliceGroup Φ Γ K s ↔ ∃ γ ∈ Γ, s⁻¹ * (Φ γ).2 * s ∈ K ∧ (Φ γ).1 = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«mem_sliceGroup» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_sliceGroup_67318eca5e77
