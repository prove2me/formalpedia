-- Prove2me | Theorems.Thm_SinkReset_Plan_short_kill
-- name    : SinkReset.Plan.short_kill
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:38.105419+00:00
-- url     : https://prove2.me/theorems/9a02e7b8-3337-5d94-9b48-768e8679b3db
-- title:
--   Plan: short kill
-- statement:
--   The Plan construction uses the short kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L471-L477
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L471-L477

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.short_kill (h : ∃ w, A.IsReset w) (S : Finset (Fin n))
    (hne : (active S).Nonempty) :
    ∃ q ∈ active S, ∃ w, A.IsWord w ∧ act w q = 0 ∧
      w.length ≤ n - (active S).card := by sorry
