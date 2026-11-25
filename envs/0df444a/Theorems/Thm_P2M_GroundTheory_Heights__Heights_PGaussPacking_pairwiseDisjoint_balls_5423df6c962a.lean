-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussPacking_pairwiseDisjoint_balls_5423df6c962a
-- name    : P2M_GroundTheory_Heights__Heights_PGaussPacking_pairwiseDisjoint_balls_5423df6c962a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:41.094711+00:00
-- url     : https://prove2.me/theorems/5d09f065-d87c-4b00-aa30-c99e3e343966
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Packing pairwise Disjoint balls 5423df6c962a: P2 M Ground Theory Heights  Heights PGauss Packing pairwise Disjoint balls 5423df6c962a
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Packing pairwise Disjoint balls 5423df6c962a construction uses the P2 M Ground Theory Heights  Heights PGauss Packing pairwise Disjoint balls 5423df6c962a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPacking.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPacking.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPacking
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
open MeasureTheory Metric
open GroundTheory.Heights₂.Heights.PGaussPacking

theorem P2M_GroundTheory_Heights__Heights_PGaussPacking_pairwiseDisjoint_balls_5423df6c962a {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ : ℝ}
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) :
    (s : Set (EuclideanSpace ℝ (Fin n))).PairwiseDisjoint (fun x => ball x (δ / 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussPacking».«pairwiseDisjoint_balls» := P2M_GroundTheory_Heights__Heights_PGaussPacking_pairwiseDisjoint_balls_5423df6c962a
