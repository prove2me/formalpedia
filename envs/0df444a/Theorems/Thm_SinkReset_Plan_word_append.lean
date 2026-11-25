-- Prove2me | Theorems.Thm_SinkReset_Plan_word_append
-- name    : SinkReset.Plan.word_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:39.530233+00:00
-- url     : https://prove2.me/theorems/7ce42e40-1f13-4eb8-aee3-4343fa82814b
-- title:
--   Plan: word append
-- statement:
--   The Plan construction uses the word append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L59-L61
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L59-L61

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.word_append (u v : List (Letter n)) :
    A.IsWord (u ++ v) ↔ A.IsWord u ∧ A.IsWord v := by sorry
