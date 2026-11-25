-- Prove2me | Theorems.Thm_SinkReset_exists_isAk_reset_ge
-- name    : SinkReset.exists_isAk_reset_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:34.068307+00:00
-- url     : https://prove2.me/theorems/4de05e8e-8bf2-4a09-b8b1-aad9f0df3913
-- title:
--   Sink Reset: exists is Ak reset ge
-- statement:
--   Lower bound. Let n ≥ 2, k ≥ 1 and either k = 1 or n ≤ k + 3. Some n-state A_k automaton with sink 0 has no reset word shorter than f k n (PROOF.md §5, Theorem, lower bound; Lemmas 12, 13, 14). Together with the upper bound this says M(n,k) = f k n.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/Solution.lean#L29-L30
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/Solution.lean#L29-L30

module
public import Mathlib
public import Definitions.Def_SinkReset
public import Definitions.Def_SinkResetThresholds_Solution
set_option autoImplicit false
@[expose] public section
public section
open SinkReset

theorem SinkReset.exists_isAk_reset_ge (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by sorry
