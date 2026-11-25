-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_norm_le_of_recurrence_growth__d6c02f29f6fb
-- name    : P2M_GlobalTheory_T_norm_le_of_recurrence_growth__d6c02f29f6fb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:39.376546+00:00
-- url     : https://prove2.me/theorems/d0383f6f-c86c-563b-af13-b3d7f6ebca9b
-- title:
--   P2 M Global Theory T norm le of recurrence growth  d6c02f29f6fb: P2 M Global Theory T norm le of recurrence growth  d6c02f29f6fb
-- statement:
--   The P2 M Global Theory T norm le of recurrence growth  d6c02f29f6fb construction uses the P2 M Global Theory T norm le of recurrence growth  d6c02f29f6fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormLeOfRecurrenceGrowthStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NormLeOfRecurrenceGrowthStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormLeOfRecurrenceGrowth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormLeOfRecurrenceGrowthStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_norm_le_of_recurrence_growth__d6c02f29f6fb : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by sorry

alias «GlobalTheory».«T».«norm_le_of_recurrence_growth'» := P2M_GlobalTheory_T_norm_le_of_recurrence_growth__d6c02f29f6fb
