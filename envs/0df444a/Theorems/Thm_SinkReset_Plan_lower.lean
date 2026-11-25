-- Prove2me | Theorems.Thm_SinkReset_Plan_lower
-- name    : SinkReset.Plan.lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:37.266967+00:00
-- url     : https://prove2.me/theorems/4db6c9b7-a153-4afb-a7bb-e76fef299271
-- title:
--   Plan: lower
-- statement:
--   The Plan construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2113-L2127
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2113-L2127

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.lower {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hnk : k = 1 ∨ n ≤ 2 * k + 1) :
    ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by sorry
