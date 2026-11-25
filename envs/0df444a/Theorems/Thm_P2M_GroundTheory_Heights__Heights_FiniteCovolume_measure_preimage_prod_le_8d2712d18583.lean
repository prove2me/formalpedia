-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_le_8d2712d18583
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_le_8d2712d18583
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:43.209905+00:00
-- url     : https://prove2.me/theorems/dc97f550-ae7a-5e24-a390-3b946b413c7b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod le 8d2712d18583: P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod le 8d2712d18583
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod le 8d2712d18583 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod le 8d2712d18583 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L70-L73

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_le_8d2712d18583 (hV : IsOpen V) (A : Set G₁) :
    μ (Φ ⁻¹' (A ×ˢ V)) ≤ sliceMeasure Φ μ V A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«measure_preimage_prod_le» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_le_8d2712d18583
