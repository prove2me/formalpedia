-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_card_le_562b29c82b98
-- name    : P2M_GroundTheory_Heights__Heights_KShort_card_le_562b29c82b98
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:52.647916+00:00
-- url     : https://prove2.me/theorems/e33599af-5e67-4bc8-9f23-2f3787993103
-- title:
--   P2 M Ground Theory Heights  Heights KShort card le 562b29c82b98: P2 M Ground Theory Heights  Heights KShort card le 562b29c82b98
-- statement:
--   The P2 M Ground Theory Heights  Heights KShort card le 562b29c82b98 construction uses the P2 M Ground Theory Heights  Heights KShort card le 562b29c82b98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L152-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L152-L221

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KShort_card_le_562b29c82b98 (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {lam r : ℝ} (hlam : 0 < lam) (hr : lam ≤ r)
    (hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    (({v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r}.ncard : ℕ) : ℝ) ≤ (3 * r / lam) ^ finrank ℝ U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KShort».«card_le» := P2M_GroundTheory_Heights__Heights_KShort_card_le_562b29c82b98
