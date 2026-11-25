-- Prove2me | Theorems.Thm_SinkReset_Plan_greedy
-- name    : SinkReset.Plan.greedy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:16.743341+00:00
-- url     : https://prove2.me/theorems/6b4d051d-3925-5b77-8317-61fc9fbb4579
-- title:
--   Plan: greedy
-- statement:
--   The Plan construction uses the greedy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1167-L1171
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1167-L1171

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n k : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.greedy (b : ℕ) (hb : n - 1 ≤ b)
    (hY : ∀ T : Finset (Fin n), T.Nonempty → T ⊆ Y A →
      ∃ w, ResetOn A T w ∧ w.length + (n - 1 - T.card) ≤ b) :
    Within A Finset.univ b := by sorry
