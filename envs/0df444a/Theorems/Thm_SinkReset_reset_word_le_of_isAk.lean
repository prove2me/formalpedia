-- Prove2me | Theorems.Thm_SinkReset_reset_word_le_of_isAk
-- name    : SinkReset.reset_word_le_of_isAk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:37.046159+00:00
-- url     : https://prove2.me/theorems/b21255bf-dde7-48fa-921e-82c5d9afde0d
-- title:
--   Sink Reset: reset word le of is Ak
-- statement:
--   Upper bound. Let k ≥ 1 and either k = 1 or n ≤ k + 3. Every n-state A_k automaton with sink 0 has a reset word of length at most f k n = ∑_{i=1}^{n-1} ⌈i/k⌉ (PROOF.md §5, Theorem, upper bound; Proposition 10).
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/Solution.lean#L25-L26
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/Solution.lean#L25-L26

module
public import Mathlib
public import Definitions.Def_SinkReset
public import Definitions.Def_SinkResetThresholds_Solution
set_option autoImplicit false
@[expose] public section
public section
open SinkReset

theorem SinkReset.reset_word_le_of_isAk (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (A : Automaton n) (hA : A.IsAk k) : ∃ w, A.IsReset w ∧ w.length ≤ f k n := by sorry
