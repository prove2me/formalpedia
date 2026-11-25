-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePacking_card_le_of_separated_2446897261d7
-- name    : P2M_GroundTheory_Heights__Heights_LatticePacking_card_le_of_separated_2446897261d7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:57.451083+00:00
-- url     : https://prove2.me/theorems/c0a28a2e-086a-469d-be50-4437a5f675f7
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Packing card le of separated 2446897261d7: P2 M Ground Theory Heights  Heights Lattice Packing card le of separated 2446897261d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Packing card le of separated 2446897261d7 construction uses the P2 M Ground Theory Heights  Heights Lattice Packing card le of separated 2446897261d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/CardLeOfSeparated.lean#L12-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/CardLeOfSeparated.lean#L12-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_CardLeOfSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module Function
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LatticePacking_card_le_of_separated_2446897261d7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) {ρ δ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ ρ) (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ ((2 * ρ + δ) / δ) ^ finrank ℝ E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticePacking».«card_le_of_separated» := P2M_GroundTheory_Heights__Heights_LatticePacking_card_le_of_separated_2446897261d7
