-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_unitBallVolume_pos_8f4cd9dcd1b0
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_unitBallVolume_pos_8f4cd9dcd1b0
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:19.651734+00:00
-- url     : https://prove2.me/theorems/32bb75c4-4cd0-485f-871f-92b46533d06f
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count unit Ball Volume pos 8f4cd9dcd1b0: P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count unit Ball Volume pos 8f4cd9dcd1
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count unit Ball Volume pos 8f4cd9dcd1b0 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count unit Ball Volume pos 8f4cd9dcd1b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L30-L31

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_unitBallVolume_pos_8f4cd9dcd1b0 (R : ℕ) : 0 < unitBallVolume R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MinkowskiCount».«unitBallVolume_pos» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_unitBallVolume_pos_8f4cd9dcd1b0
