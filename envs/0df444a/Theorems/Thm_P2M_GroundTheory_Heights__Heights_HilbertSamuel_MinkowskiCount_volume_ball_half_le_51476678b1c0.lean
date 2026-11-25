-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_half_le_51476678b1c0
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_half_le_51476678b1c0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:53.309581+00:00
-- url     : https://prove2.me/theorems/9664265e-a350-5ef8-a2f3-6fdf557fd970
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count volume ball half le 51476678b1c0: P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count volume ball half le 51476678b1c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count volume ball half le 51476678b1c0 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count volume ball half le 51476678b1c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L42-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L42-L85

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_half_le_51476678b1c0 (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ) {F : Set V}
    (fund : IsAddFundamentalDomain La F volume) :
    volume (ball (0 : V) (ρ / 2)) ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ≥0∞) * volume F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MinkowskiCount».«volume_ball_half_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_half_le_51476678b1c0
