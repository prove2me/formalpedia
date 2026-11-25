-- Prove2me | Theorems.Thm_UpperTheory_T3_levelPrimeN
-- name    : UpperTheory.T3.levelPrimeN
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:04:49.96858+00:00
-- url     : https://prove2.me/theorems/44d5604f-90ce-4fd9-a334-78d0edb15785
-- title:
--   T3: level Prime N
-- statement:
--   The T3 construction uses the level Prime N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/levelPrimeN.lean#L36-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/levelPrimeN.lean#L36-L161

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_levelPrimeN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Mem.An
open UpperTheory UpperTheory.T3
set_option maxHeartbeats 800000

theorem UpperTheory.T3.levelPrimeN :
    ShortNorm → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ cs CY : ℝ, 0 < cs → 0 < CY → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ N d g₁ g₂ m : ℕ,
      ModAt x eps N d → 1 ≤ g₁ → 1 ≤ g₂ → Real.log g₁ ≤ CY * x ^ eps → Real.log g₂ ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m →
      ∀ V Ts : ℝ, 1 ≤ V → V ≤ x ^ (12 : ℝ) → 0 < Ts → cs * m * x ^ eps ≤ Real.log Ts →
      ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / V) * Ts ∧ NormOne d (N * (g₁ * g₂) ^ 2) T := by sorry
