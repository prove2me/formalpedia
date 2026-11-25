-- Prove2me | Theorems.Thm_SinkReset_Plan_f_split
-- name    : SinkReset.Plan.f_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:31.497045+00:00
-- url     : https://prove2.me/theorems/39ecb0d9-b575-4aa8-8dac-58fbd294db32
-- title:
--   Plan: f split
-- statement:
--   The Plan construction uses the f split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L763-L775
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L763-L775

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.f_split {k c d : ℕ} (hk : 1 ≤ k) :
    f k (c + 1) + f k (d + 1) ≤ f k (c + d + 1) := by sorry
