-- Prove2me | Theorems.Thm_SinkReset_Plan_upper
-- name    : SinkReset.Plan.upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:40.499264+00:00
-- url     : https://prove2.me/theorems/0623d645-d728-5619-9fa7-1a54302ebac9
-- title:
--   Plan: upper
-- statement:
--   The Plan construction uses the upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1184-L1186
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1184-L1186

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n k : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.upper (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) (hA : A.IsAk k) :
    Within A Finset.univ (f k n) := by sorry
