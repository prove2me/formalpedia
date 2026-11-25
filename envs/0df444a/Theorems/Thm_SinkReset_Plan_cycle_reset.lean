-- Prove2me | Theorems.Thm_SinkReset_Plan_cycle_reset
-- name    : SinkReset.Plan.cycle_reset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:51.363834+00:00
-- url     : https://prove2.me/theorems/e44f9e69-6777-5031-8a53-27d95d4d37b8
-- title:
--   Plan: cycle reset
-- statement:
--   The Plan construction uses the cycle reset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1543-L1632
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1543-L1632

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.cycle_reset {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ w, (cycle k m).IsReset w ∧ w.length = k + 2 * m := by sorry
