-- Prove2me | Theorems.Thm_SinkReset_Plan_act_append
-- name    : SinkReset.Plan.act_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:23.827117+00:00
-- url     : https://prove2.me/theorems/2f0f4715-02c7-5bea-8cbb-023bdc246bb9
-- title:
--   Plan: act append
-- statement:
--   The Plan construction uses the act append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L56-L58
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L56-L58

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.act_append (u v : List (Letter n)) (q : Fin n) :
    act (u ++ v) q = act v (act u q) := by sorry
