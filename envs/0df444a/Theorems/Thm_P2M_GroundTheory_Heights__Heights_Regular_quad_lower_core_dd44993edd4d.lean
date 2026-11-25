-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_quad_lower_core_dd44993edd4d
-- name    : P2M_GroundTheory_Heights__Heights_Regular_quad_lower_core_dd44993edd4d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:29.66213+00:00
-- url     : https://prove2.me/theorems/60e9483c-36b3-4be9-8610-d87e38d33eb4
-- title:
--   P2 M Ground Theory Heights  Heights Regular quad lower core dd44993edd4d: P2 M Ground Theory Heights  Heights Regular quad lower core dd44993edd4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular quad lower core dd44993edd4d construction uses the P2 M Ground Theory Heights  Heights Regular quad lower core dd44993edd4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L72-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L72-L145

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

theorem P2M_GroundTheory_Heights__Heights_Regular_quad_lower_core_dd44993edd4d {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K W : Set Z}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M W)
    (S : Matrix (Fin g) (Fin g) ℝ) (hS : S.PosSemidef)
    (hpos : ∀ z ∈ K, ∀ v : Fin g → ℝ, v ≠ 0 → S *ᵥ v = 0 → 0 < v ⬝ᵥ M z *ᵥ v) :
    ∃ L ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ,
      ε * (v ⬝ᵥ v) ≤ L * (v ⬝ᵥ S *ᵥ v) + v ⬝ᵥ M z *ᵥ v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«quad_lower_core» := P2M_GroundTheory_Heights__Heights_Regular_quad_lower_core_dd44993edd4d
