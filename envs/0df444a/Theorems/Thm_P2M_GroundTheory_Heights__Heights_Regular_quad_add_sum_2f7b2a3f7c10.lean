-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_quad_add_sum_2f7b2a3f7c10
-- name    : P2M_GroundTheory_Heights__Heights_Regular_quad_add_sum_2f7b2a3f7c10
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:58.482817+00:00
-- url     : https://prove2.me/theorems/888e1de1-5975-4714-9c1b-0d5af00fec15
-- title:
--   P2 M Ground Theory Heights  Heights Regular quad add sum 2f7b2a3f7c10: P2 M Ground Theory Heights  Heights Regular quad add sum 2f7b2a3f7c10
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular quad add sum 2f7b2a3f7c10 construction uses the P2 M Ground Theory Heights  Heights Regular quad add sum 2f7b2a3f7c10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L166-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L166-L172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_quad_add_sum_2f7b2a3f7c10 {g a : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (l : Fin a → ℝ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    v ⬝ᵥ (A + ∑ i, l i • B i) *ᵥ v = v ⬝ᵥ A *ᵥ v + ∑ i, l i * (v ⬝ᵥ B i *ᵥ v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«quad_add_sum» := P2M_GroundTheory_Heights__Heights_Regular_quad_add_sum_2f7b2a3f7c10
