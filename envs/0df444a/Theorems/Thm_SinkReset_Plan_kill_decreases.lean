-- Prove2me | Theorems.Thm_SinkReset_Plan_kill_decreases
-- name    : SinkReset.Plan.kill_decreases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:54.581938+00:00
-- url     : https://prove2.me/theorems/77f5bf0f-4ede-44d6-96ac-e342988012bd
-- title:
--   Plan: kill decreases
-- statement:
--   The Plan construction uses the kill decreases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L103-L106
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L103-L106

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.kill_decreases (S : Finset (Fin n)) (q : Fin n) (hq : q ∈ active S)
    (w : List (Letter n)) (hw : A.IsWord w) (hkill : act w q = 0) :
    (active (S.image (act w))).card + 1 ≤ (active S).card := by sorry
