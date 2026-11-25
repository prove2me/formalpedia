-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_log_count_deff93b91d06
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_log_count_deff93b91d06
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:54.251561+00:00
-- url     : https://prove2.me/theorems/3d4093d1-c2f8-4168-aa0a-00f654e29cf1
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count log count deff93b91d06: P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count log count deff93b91d06
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count log count deff93b91d06 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Minkowski Count log count deff93b91d06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L87-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMinkowskiCount.lean#L87-L113

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_log_count_deff93b91d06 (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ)
    (hρ : 0 < ρ) :
    Real.log (unitBallVolume (finrank ℝ V)) + (finrank ℝ V : ℝ) * Real.log (ρ / 2) -
        Real.log (ZLattice.covolume La) ≤
      Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MinkowskiCount».«log_count» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_log_count_deff93b91d06
