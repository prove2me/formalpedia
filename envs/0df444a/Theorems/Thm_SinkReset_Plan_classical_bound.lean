-- Prove2me | Theorems.Thm_SinkReset_Plan_classical_bound
-- name    : SinkReset.Plan.classical_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:05.547208+00:00
-- url     : https://prove2.me/theorems/ee29db78-4d86-4cbc-8c8e-da5a1eaa310b
-- title:
--   Plan: classical bound
-- statement:
--   The Plan construction uses the classical bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L478-L483
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L478-L483

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.classical_bound (h : ∃ w, A.IsReset w) (S : Finset (Fin n)) :
    Within A S (∑ j ∈ Finset.range (active S).card, (n - (j + 1))) := by sorry
