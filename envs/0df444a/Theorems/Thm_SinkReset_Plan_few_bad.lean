-- Prove2me | Theorems.Thm_SinkReset_Plan_few_bad
-- name    : SinkReset.Plan.few_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:23.617549+00:00
-- url     : https://prove2.me/theorems/a1afe386-e1bb-465d-8d04-8d0dfc5e9584
-- title:
--   Plan: few bad
-- statement:
--   The Plan construction uses the few bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1128-L1130
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1128-L1130

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n k : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.few_bad (hk : 1 ≤ k) (hA : A.IsAk k) (hsc : SC A) :
    ((Y A).Nonempty → k ≤ (Z A).card) ∧ (Y A).card ≤ n - 1 - k := by sorry
