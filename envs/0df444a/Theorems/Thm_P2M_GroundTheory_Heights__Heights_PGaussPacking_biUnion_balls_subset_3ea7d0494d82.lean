-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussPacking_biUnion_balls_subset_3ea7d0494d82
-- name    : P2M_GroundTheory_Heights__Heights_PGaussPacking_biUnion_balls_subset_3ea7d0494d82
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:27.031837+00:00
-- url     : https://prove2.me/theorems/72e853f4-60e2-44c7-8ede-a6552b1c4796
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Packing bi Union balls subset 3ea7d0494d82: P2 M Ground Theory Heights  Heights PGauss Packing bi Union balls subset 3ea7d0494d82
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Packing bi Union balls subset 3ea7d0494d82 construction uses the P2 M Ground Theory Heights  Heights PGauss Packing bi Union balls subset 3ea7d0494d82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPacking.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussPacking.lean#L19-L30

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

theorem P2M_GroundTheory_Heights__Heights_PGaussPacking_biUnion_balls_subset_3ea7d0494d82 {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) {δ r : ℝ}
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) :
    (⋃ x ∈ s, ball x (δ / 2)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussPacking».«biUnion_balls_subset» := P2M_GroundTheory_Heights__Heights_PGaussPacking_biUnion_balls_subset_3ea7d0494d82
