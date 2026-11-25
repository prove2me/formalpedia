-- Prove2me | Theorems.Thm_SinkReset_Plan_act_zero
-- name    : SinkReset.Plan.act_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:36.997723+00:00
-- url     : https://prove2.me/theorems/18ff5b1d-58b9-48e0-b2e8-3317be841d01
-- title:
--   Plan: act zero
-- statement:
--   The Plan construction uses the act zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L62-L71
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L62-L71

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.act_zero (w : List (Letter n)) (hw : A.IsWord w) :
    act w 0 = 0 := by sorry
