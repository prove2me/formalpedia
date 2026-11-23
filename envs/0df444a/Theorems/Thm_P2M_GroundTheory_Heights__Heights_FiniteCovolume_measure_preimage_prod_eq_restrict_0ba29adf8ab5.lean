-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_eq_restrict_0ba29adf8ab5
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_eq_restrict_0ba29adf8ab5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:23.974004+00:00
-- url     : https://prove2.me/theorems/fef5af86-a957-4f4c-87d7-ecf7a725d023
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod eq restrict 0ba29adf8ab5: P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod eq restrict 0ba29adf8ab5
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod eq restrict 0ba29adf8ab5 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume measure preimage prod eq restrict 0ba29adf8ab5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L61-L63

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_eq_restrict_0ba29adf8ab5 (hV : IsOpen V) (A : Set G₁) :
    μ (Φ ⁻¹' (A ×ˢ V)) = μ.restrict (Φ ⁻¹' (univ ×ˢ V)) ((fun x => (Φ x).1) ⁻¹' A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«measure_preimage_prod_eq_restrict» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_eq_restrict_0ba29adf8ab5
