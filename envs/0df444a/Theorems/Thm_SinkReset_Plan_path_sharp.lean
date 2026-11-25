-- Prove2me | Theorems.Thm_SinkReset_Plan_path_sharp
-- name    : SinkReset.Plan.path_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:08.712195+00:00
-- url     : https://prove2.me/theorems/488bb97f-ca7a-4de3-9733-66cd04fcd30c
-- title:
--   Plan: path sharp
-- statement:
--   The Plan construction uses the path sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1365-L1398
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1365-L1398

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.path_sharp {n k : ℕ} [NeZero n] (hk : 1 ≤ k) :
    (path n).IsAk k ∧
    (∃ w, (path n).IsReset w ∧ w.length = n - 1) ∧
    ∀ w, (path n).IsReset w → n - 1 ≤ w.length := by sorry
