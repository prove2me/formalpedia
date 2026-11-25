-- Prove2me | Theorems.Thm_SinkReset_Plan_f_small
-- name    : SinkReset.Plan.f_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:24.955335+00:00
-- url     : https://prove2.me/theorems/feb87716-a672-5944-9e29-dacb6b76056b
-- title:
--   Plan: f small
-- statement:
--   The Plan construction uses the f small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L739-L749
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L739-L749

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.f_small {k n : ℕ} (hk : 1 ≤ k) (hn : n ≤ k + 1) :
    f k n = n - 1 := by sorry
