-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_fst_comp_ffba65d6ed46
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_fst_comp_ffba65d6ed46
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:27.13081+00:00
-- url     : https://prove2.me/theorems/00cd15bc-c0a3-46f3-812f-f99d69369e74
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume measurable fst comp ffba65d6ed46: P2 M Ground Theory Heights  Heights Finite Covolume measurable fst comp ffba65d6ed46
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume measurable fst comp ffba65d6ed46 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume measurable fst comp ffba65d6ed46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean#L50-L51

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_fst_comp_ffba65d6ed46 (Φ : G ≃ₜ* G₁ × G₂) : Measurable fun x => (Φ x).1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«measurable_fst_comp» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_fst_comp_ffba65d6ed46
