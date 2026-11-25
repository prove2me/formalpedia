-- Prove2me | Theorems.Thm_SinkReset_Plan_transposition_reset
-- name    : SinkReset.Plan.transposition_reset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:26.066261+00:00
-- url     : https://prove2.me/theorems/ecea26ab-f166-5cbb-b59e-12746e5842ad
-- title:
--   Plan: transposition reset
-- statement:
--   The Plan construction uses the transposition reset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1303-L1332
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1303-L1332

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.transposition_reset {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ∃ w, (transposition n).IsReset w ∧ w.length = n * (n - 1) / 2 := by sorry
