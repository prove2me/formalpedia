-- Prove2me | Theorems.Thm_SinkReset_five_two_reset_word_le_dev
-- name    : SinkReset.five_two_reset_word_le_dev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:06.974214+00:00
-- url     : https://prove2.me/theorems/f2a054d4-fe3e-4ffa-8bdb-6b13445155e5
-- title:
--   Sink Reset: five two reset word le dev
-- statement:
--   The Sink Reset construction uses the five two reset word le dev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2139-L2142
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2139-L2142

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset

theorem SinkReset.five_two_reset_word_le_dev (A : Automaton 5) (hA : A.IsAk 2) : ∃ w, A.IsReset w ∧ w.length ≤ 6 := by sorry
