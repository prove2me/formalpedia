-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_quad_upper_core_c53c0b0b1192
-- name    : P2M_GroundTheory_Heights__Heights_Regular_quad_upper_core_c53c0b0b1192
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:27.870847+00:00
-- url     : https://prove2.me/theorems/e95a22a6-c7c6-5792-a238-5d18693649a1
-- title:
--   P2 M Ground Theory Heights  Heights Regular quad upper core c53c0b0b1192: P2 M Ground Theory Heights  Heights Regular quad upper core c53c0b0b1192
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular quad upper core c53c0b0b1192 construction uses the P2 M Ground Theory Heights  Heights Regular quad upper core c53c0b0b1192 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L51-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L51-L70

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

theorem P2M_GroundTheory_Heights__Heights_Regular_quad_upper_core_c53c0b0b1192 {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K : Set Z} (hK : IsCompact K)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ, v ⬝ᵥ M z *ᵥ v ≤ A * (v ⬝ᵥ v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«quad_upper_core» := P2M_GroundTheory_Heights__Heights_Regular_quad_upper_core_c53c0b0b1192
