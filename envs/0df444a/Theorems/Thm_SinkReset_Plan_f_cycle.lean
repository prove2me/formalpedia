-- Prove2me | Theorems.Thm_SinkReset_Plan_f_cycle
-- name    : SinkReset.Plan.f_cycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:57.542946+00:00
-- url     : https://prove2.me/theorems/05eb0c64-9ef9-5d01-a681-9a9f4b060022
-- title:
--   Plan: f cycle
-- statement:
--   The Plan construction uses the f cycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L760-L762
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L760-L762

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.f_cycle {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k) :
    f k (k + m + 1) = k + 2 * m := by sorry
