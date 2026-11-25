-- Prove2me | Theorems.Thm_SinkReset_reset_word_le_of_isAk_dev
-- name    : SinkReset.reset_word_le_of_isAk_dev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:43.740517+00:00
-- url     : https://prove2.me/theorems/25a6a6a5-ba9a-4bca-a292-1c4e25db36cb
-- title:
--   Sink Reset: reset word le of is Ak dev
-- statement:
--   The Sink Reset construction uses the reset word le of is Ak dev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2132-L2133
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2132-L2133

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset

theorem SinkReset.reset_word_le_of_isAk_dev (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (A : Automaton n) (hA : A.IsAk k) : ∃ w, A.IsReset w ∧ w.length ≤ f k n := by sorry
