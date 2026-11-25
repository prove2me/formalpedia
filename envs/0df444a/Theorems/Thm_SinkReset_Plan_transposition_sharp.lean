-- Prove2me | Theorems.Thm_SinkReset_Plan_transposition_sharp
-- name    : SinkReset.Plan.transposition_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:49.380958+00:00
-- url     : https://prove2.me/theorems/0776db3c-6ac0-4d61-9c78-df45910ad5dc
-- title:
--   Plan: transposition sharp
-- statement:
--   The Plan construction uses the transposition sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1333-L1339
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1333-L1339

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.transposition_sharp {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (transposition n).IsAk 1 ∧
    ∀ w, (transposition n).IsReset w → f 1 n ≤ w.length := by sorry
