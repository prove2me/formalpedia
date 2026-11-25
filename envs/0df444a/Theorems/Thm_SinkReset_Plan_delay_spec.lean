-- Prove2me | Theorems.Thm_SinkReset_Plan_delay_spec
-- name    : SinkReset.Plan.delay_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:29.21827+00:00
-- url     : https://prove2.me/theorems/3f6627c8-c4f6-44e4-b937-38fe543e560f
-- title:
--   Plan: delay spec
-- statement:
--   The Plan construction uses the delay spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1644-L1664
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1644-L1664

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.delay_spec {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (S : Finset (Fin (k + m + 1))) :
    delay k m S ≤ m ∧
    ((active S).Nonempty → ∃ q ∈ active S, cycleDelta k m q = delay k m S) ∧
    (∀ q ∈ active S, delay k m S ≤ cycleDelta k m q) := by sorry
