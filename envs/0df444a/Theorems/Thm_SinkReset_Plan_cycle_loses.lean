-- Prove2me | Theorems.Thm_SinkReset_Plan_cycle_loses
-- name    : SinkReset.Plan.cycle_loses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:28.200977+00:00
-- url     : https://prove2.me/theorems/3ef43222-486d-58f2-8af7-e22385336a3e
-- title:
--   Plan: cycle loses
-- statement:
--   The Plan construction uses the cycle loses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1783-L1819
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1783-L1819

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.cycle_loses {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ¬ (cycle k m).IsAk (k + 1) := by sorry
