-- Prove2me | Theorems.Thm_SinkReset_Plan_two_bad
-- name    : SinkReset.Plan.two_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:34.120568+00:00
-- url     : https://prove2.me/theorems/b83f6d37-38c2-423a-b888-5c5b126de832
-- title:
--   Plan: two bad
-- statement:
--   The Plan construction uses the two bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1173-L1178
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1173-L1178

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n k : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.two_bad (hk : 2 ≤ k) (hA : A.IsAk k) (hcard : (Y A).card ≤ 2)
    (T : Finset (Fin n)) (hT : T ⊆ Y A) (hsize : T.card = 2) :
    Within A T 4 := by sorry
