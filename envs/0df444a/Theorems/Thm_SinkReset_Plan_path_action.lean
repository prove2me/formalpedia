-- Prove2me | Theorems.Thm_SinkReset_Plan_path_action
-- name    : SinkReset.Plan.path_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:31.043156+00:00
-- url     : https://prove2.me/theorems/2f5d10a6-2fc2-5a22-9773-7b95e66fc64b
-- title:
--   Plan: path action
-- statement:
--   The Plan construction uses the path action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1353-L1364
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1353-L1364

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.path_action {n : ℕ} [NeZero n] (w : List (Letter n))
    (hw : (path n).IsWord w) (q : Fin n) :
    (act w q).val = q.val - w.length := by sorry
