-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_exists_near_91c44c1fd18c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_exists_near_91c44c1fd18c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:03.073971+00:00
-- url     : https://prove2.me/theorems/29882461-c81c-5991-afef-53a2f162efd0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Lattice Count exists near 91c44c1fd18c: P2 M Ground Theory Heights  Heights Hilbert Samuel Lattice Count exists near 91c44c1fd18c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Lattice Count exists near 91c44c1fd18c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Lattice Count exists near 91c44c1fd18c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PLatticeCount.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PLatticeCount.lean#L17-L33

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_exists_near_91c44c1fd18c (B : ShortLatticeBasis La c) (x : V) :
    ∃ μ ∈ La, ‖x + μ‖ ≤ finrank ℝ V * c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«LatticeCount».«exists_near» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_exists_near_91c44c1fd18c
