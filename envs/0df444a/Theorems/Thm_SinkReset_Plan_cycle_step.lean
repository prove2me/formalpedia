-- Prove2me | Theorems.Thm_SinkReset_Plan_cycle_step
-- name    : SinkReset.Plan.cycle_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:10.255352+00:00
-- url     : https://prove2.me/theorems/afd437e1-72e1-4907-9195-15543e978392
-- title:
--   Plan: cycle step
-- statement:
--   The Plan construction uses the cycle step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1467-L1490
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1467-L1490

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.cycle_step {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (a : Letter (k + m + 1)) (ha : a ∈ (cycle k m).letters)
    (S : Finset (Fin (k + m + 1))) :
    potential (cycleWeight k m) S ≤ potential (cycleWeight k m) (S.image a) + 1 := by sorry
