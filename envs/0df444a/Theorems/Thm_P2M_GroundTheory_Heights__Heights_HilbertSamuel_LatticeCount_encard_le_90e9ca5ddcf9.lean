-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_encard_le_90e9ca5ddcf9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_encard_le_90e9ca5ddcf9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:09.036587+00:00
-- url     : https://prove2.me/theorems/29569d6c-dbf1-5d1b-8a77-fea6f6acab67
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Lattice Count encard le 90e9ca5ddcf9: P2 M Ground Theory Heights  Heights Hilbert Samuel Lattice Count encard le 90e9ca5ddcf9
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Lattice Count encard le 90e9ca5ddcf9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Lattice Count encard le 90e9ca5ddcf9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PLatticeCount.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PLatticeCount.lean#L35-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PLatticeCount
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
open MeasureTheory Metric Module ZSpan
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (La : Submodule ℤ V) {c : ℝ}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_encard_le_90e9ca5ddcf9 (B : ShortLatticeBasis La c) (b : ℝ) (x : V) :
    {y : V | y ∈ La ∧ ‖y‖ ≤ b}.encard ≤
      {g : La | g +ᵥ x ∈ closedBall (0 : V) (b + finrank ℝ V * c)}.encard := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«LatticeCount».«encard_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_encard_le_90e9ca5ddcf9
