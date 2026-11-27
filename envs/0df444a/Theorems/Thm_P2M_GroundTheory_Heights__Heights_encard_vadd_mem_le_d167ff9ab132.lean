-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_encard_vadd_mem_le_d167ff9ab132
-- name    : P2M_GroundTheory_Heights__Heights_encard_vadd_mem_le_d167ff9ab132
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:49.004928+00:00
-- url     : https://prove2.me/theorems/85860650-e90e-444e-a379-cd2f8d822009
-- title:
--   P2 M Ground Theory Heights  Heights encard vadd mem le d167ff9ab132: P2 M Ground Theory Heights  Heights encard vadd mem le d167ff9ab132
-- statement:
--   The P2 M Ground Theory Heights  Heights encard vadd mem le d167ff9ab132 construction uses the P2 M Ground Theory Heights  Heights encard vadd mem le d167ff9ab132 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CovolumeCount.lean#L30-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CovolumeCount.lean#L30-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module ZSpan NumberField
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L]
variable [IsZLattice ℝ L]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [DiscreteTopology L] [IsZLattice ℝ L]

theorem P2M_GroundTheory_Heights__Heights_encard_vadd_mem_le_d167ff9ab132 (x : V) :
    {g : L | g +ᵥ x ∈ closedBall (0 : V) (1 / 2)}.encard ≤
      {y : V | y ∈ L ∧ ‖y‖ ≤ 1}.encard := by sorry

alias «GroundTheory».«Heights₂».«Heights».«encard_vadd_mem_le» := P2M_GroundTheory_Heights__Heights_encard_vadd_mem_le_d167ff9ab132
