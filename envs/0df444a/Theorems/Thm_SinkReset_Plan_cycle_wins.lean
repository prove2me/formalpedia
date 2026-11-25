-- Prove2me | Theorems.Thm_SinkReset_Plan_cycle_wins
-- name    : SinkReset.Plan.cycle_wins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:22.1648+00:00
-- url     : https://prove2.me/theorems/b28212d2-e354-5edd-b03f-e976e2930a3c
-- title:
--   Plan: cycle wins
-- statement:
--   The Plan construction uses the cycle wins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1769-L1771
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1769-L1771

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.cycle_wins {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (cycle k m).IsAk k := by sorry
