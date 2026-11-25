-- Prove2me | Theorems.Thm_SinkReset_Plan_transposition_step
-- name    : SinkReset.Plan.transposition_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:38.234869+00:00
-- url     : https://prove2.me/theorems/6d5e4588-18cf-4679-8864-43d3e2a83896
-- title:
--   Plan: transposition step
-- statement:
--   The Plan construction uses the transposition step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1282-L1298
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1282-L1298

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.transposition_step {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a : Letter n) (ha : a ∈ (transposition n).letters) (S : Finset (Fin n)) :
    potential Fin.val S ≤ potential Fin.val (S.image a) + 1 := by sorry
