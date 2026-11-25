-- Prove2me | Theorems.Thm_SinkReset_Plan_within_univ
-- name    : SinkReset.Plan.within_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:44.259804+00:00
-- url     : https://prove2.me/theorems/1432bcce-39f5-4a11-bcb8-851b20df40e9
-- title:
--   Plan: within univ
-- statement:
--   The Plan construction uses the within univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L114-L120
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L114-L120

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.within_univ (b : ℕ) :
    Within A Finset.univ b ↔ ∃ w, A.IsReset w ∧ w.length ≤ b := by sorry
