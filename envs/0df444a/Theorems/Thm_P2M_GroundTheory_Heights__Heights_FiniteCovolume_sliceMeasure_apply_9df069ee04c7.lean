-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_apply_9df069ee04c7
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_apply_9df069ee04c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:14.371984+00:00
-- url     : https://prove2.me/theorems/043efeea-6803-47dd-b9aa-9fe60a780483
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume slice Measure apply 9df069ee04c7: P2 M Ground Theory Heights  Heights Finite Covolume slice Measure apply 9df069ee04c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume slice Measure apply 9df069ee04c7 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume slice Measure apply 9df069ee04c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L65-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
set_option linter.unusedSectionVars false
noncomputable section
variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_apply_9df069ee04c7 (hV : IsOpen V) {A : Set G₁} (hA : MeasurableSet A) :
    sliceMeasure Φ μ V A = μ (Φ ⁻¹' (A ×ˢ V)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«sliceMeasure_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_apply_9df069ee04c7
