-- Prove2me | Theorems.Thm_SinkReset_Plan_reachable_reset
-- name    : SinkReset.Plan.reachable_reset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:08.864087+00:00
-- url     : https://prove2.me/theorems/651290c5-e886-5353-871d-596be346cf16
-- title:
--   Plan: reachable reset
-- statement:
--   The Plan construction uses the reachable reset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L442-L447
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L442-L447

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.reachable_reset
    (h : ∀ q, ∃ w, A.IsWord w ∧ act w q = 0) (S : Finset (Fin n)) :
    ∃ w, ResetOn A S w := by sorry
