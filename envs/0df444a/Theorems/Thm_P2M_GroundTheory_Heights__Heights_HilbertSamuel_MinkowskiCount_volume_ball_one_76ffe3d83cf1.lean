-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_one_76ffe3d83cf1
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_one_76ffe3d83cf1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:18.564873+00:00
-- url     : https://prove2.me/theorems/a2f95895-0fb6-42e9-803c-ee1fcf4dd474
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count volume ball one 76ffe3d83cf1: P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count volume ball one 76ffe3d83cf1
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count volume ball one 76ffe3d83cf1 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count volume ball one 76ffe3d83cf1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L33-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_one_76ffe3d83cf1 :
    volume (ball (0 : V) 1) = ENNReal.ofReal (unitBallVolume (finrank ℝ V)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MinkowskiCount».«volume_ball_one» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_one_76ffe3d83cf1
