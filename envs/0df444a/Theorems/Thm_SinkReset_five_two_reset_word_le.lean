-- Prove2me | Theorems.Thm_SinkReset_five_two_reset_word_le
-- name    : SinkReset.five_two_reset_word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:55.845648+00:00
-- url     : https://prove2.me/theorems/03ab689c-5852-433a-9ba7-cc4b3f415130
-- title:
--   Sink Reset: five two reset word le
-- statement:
--   M(5,2) ≤ 6: every 5-state A_2 automaton with sink 0 has a reset word of length at most 6 (CLAIM.md headline; PROOF.md §5, the pair (5,2)).
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/Solution.lean#L33-L34
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/Solution.lean#L33-L34

module
public import Mathlib
public import Definitions.Def_SinkReset
public import Definitions.Def_SinkResetThresholds_Solution
set_option autoImplicit false
@[expose] public section
public section
open SinkReset

theorem SinkReset.five_two_reset_word_le (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6 := by sorry
