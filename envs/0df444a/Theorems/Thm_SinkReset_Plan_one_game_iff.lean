-- Prove2me | Theorems.Thm_SinkReset_Plan_one_game_iff
-- name    : SinkReset.Plan.one_game_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:43.95558+00:00
-- url     : https://prove2.me/theorems/4a325937-4b3d-4a3b-a126-e363df2eafdb
-- title:
--   Plan: one game iff
-- statement:
--   The Plan construction uses the one game iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L162-L181
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L162-L181

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.one_game_iff : A.IsAk 1 ↔ ∃ w, A.IsReset w := by sorry
