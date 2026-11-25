-- Prove2me | Theorems.Thm_SinkReset_Plan_cycle_sum
-- name    : SinkReset.Plan.cycle_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:50.037967+00:00
-- url     : https://prove2.me/theorems/f24001b3-4dcf-5250-b06f-2df4a8bf4b60
-- title:
--   Plan: cycle sum
-- statement:
--   The Plan construction uses the cycle sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1491-L1527
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1491-L1527

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.cycle_sum {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    potential (cycleWeight k m) Finset.univ = k + 2 * m := by sorry
