-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_eq_smul_haar_b8209152515f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_eq_smul_haar_b8209152515f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:29.715801+00:00
-- url     : https://prove2.me/theorems/89cb2cb5-1fb5-4dce-8f1b-0cb31cd8982b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume slice Measure eq smul haar b8209152515f: P2 M Ground Theory Heights  Heights Finite Covolume slice Measure eq smul haar b8209152515f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume slice Measure eq smul haar b8209152515f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume slice Measure eq smul haar b8209152515f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L95-L99

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
variable [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [μ.IsHaarMeasure]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_eq_smul_haar_b8209152515f (hV : IsOpen V) (hVc : IsCompact V) :
    ∃ c : ℝ≥0, sliceMeasure Φ μ V = c • Measure.haar := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«sliceMeasure_eq_smul_haar» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_eq_smul_haar_b8209152515f
