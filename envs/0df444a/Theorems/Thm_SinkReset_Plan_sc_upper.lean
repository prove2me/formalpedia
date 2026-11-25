-- Prove2me | Theorems.Thm_SinkReset_Plan_sc_upper
-- name    : SinkReset.Plan.sc_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:33.560808+00:00
-- url     : https://prove2.me/theorems/ff3e4f8b-4b74-5f8f-b66d-cc18363e1234
-- title:
--   Plan: sc upper
-- statement:
--   The Plan construction uses the sc upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1180-L1182
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1180-L1182

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n k : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.sc_upper (hk : 2 ≤ k) (hA : A.IsAk k) (hsc : SC A)
    (hn : n ≤ k + 3) : Within A Finset.univ (f k n) := by sorry
