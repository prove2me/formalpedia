-- Prove2me | Theorems.Thm_SinkReset_Plan_cycle_sharp
-- name    : SinkReset.Plan.cycle_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:27.266769+00:00
-- url     : https://prove2.me/theorems/53911bba-ef03-5afb-9f49-9b4c856ca05f
-- title:
--   Plan: cycle sharp
-- statement:
--   The Plan construction uses the cycle sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1821-L1828
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1821-L1828

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.cycle_sharp {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (cycle k m).IsAk k ∧
    (∃ w, (cycle k m).IsReset w ∧ w.length = k + 2 * m) ∧
    (∀ w, (cycle k m).IsReset w → k + 2 * m ≤ w.length) ∧
    ¬ (cycle k m).IsAk (k + 1) := by sorry
