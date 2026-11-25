-- Prove2me | Theorems.Thm_SinkReset_Plan_wins_word
-- name    : SinkReset.Plan.wins_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:20.735698+00:00
-- url     : https://prove2.me/theorems/064d9abe-508e-4752-b010-c7fbf01eb2a0
-- title:
--   Plan: wins word
-- statement:
--   The Plan construction uses the wins word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L129-L139
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L129-L139

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.wins_word {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (h : A.AliceWins k S) : ∃ w, ResetOn A S w := by sorry
