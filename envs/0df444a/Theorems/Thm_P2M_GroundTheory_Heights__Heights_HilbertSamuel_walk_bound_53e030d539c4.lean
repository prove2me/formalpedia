-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_walk_bound_53e030d539c4
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_walk_bound_53e030d539c4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:12.76755+00:00
-- url     : https://prove2.me/theorems/36eef61f-5fc9-4678-b24f-67ea788c60af
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel walk bound 53e030d539c4: P2 M Ground Theory Heights  Heights Hilbert Samuel walk bound 53e030d539c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel walk bound 53e030d539c4 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel walk bound 53e030d539c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L17-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L17-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_walk_bound_53e030d539c4 (g : (K → ℕ) → ℝ) (a₀ : ℕ) (B : ℝ) (hB : 0 ≤ B) (n : ℕ)
    (hstep : ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) → ∀ b, a₀ < a b →
      |g a - g (Function.update a b (a b - 1))| ≤ B * ((∑ k, (a k : ℝ)) + 1) ^ n) :
    ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |g a| ≤ |g (fun _ => a₀)| + B * ((∑ k, (a k : ℝ)) + 1) ^ (n + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«walk_bound» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_walk_bound_53e030d539c4
