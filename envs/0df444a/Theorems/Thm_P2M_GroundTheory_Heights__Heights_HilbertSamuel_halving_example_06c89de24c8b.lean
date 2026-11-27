-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_halving_example_06c89de24c8b
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_halving_example_06c89de24c8b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:35.052836+00:00
-- url     : https://prove2.me/theorems/9208ef9a-d95a-5c0b-bbdd-6ca9165b1fcb
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel halving example 06c89de24c8b: P2 M Ground Theory Heights  Heights Hilbert Samuel halving example 06c89de24c8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel halving example 06c89de24c8b construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel halving example 06c89de24c8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsLattice.lean#L132-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsLattice.lean#L132-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt MeasureTheory Module Filter
  Topology Asymptotics Matrix
open scoped ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_halving_example_06c89de24c8b :
    (∃ C : ℝ, ∀ n : ℕ, |1 / ((n : ℝ) + 1)| ≤ C) ∧
    Tendsto (fun n : ℕ ↦ 1 / (((2 * n : ℕ) : ℝ) + 1) - 1 / ((n : ℝ) + 1) / 2) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) + 1) - 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«halving_example» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_halving_example_06c89de24c8b
