-- Prove2me | Theorems.Thm_SinkReset_Plan_closed_reduction
-- name    : SinkReset.Plan.closed_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:41.672983+00:00
-- url     : https://prove2.me/theorems/8b5fde55-82a4-4526-abe0-28a782088783
-- title:
--   Plan: closed reduction
-- statement:
--   The Plan construction uses the closed reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L637-L727
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L637-L727

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.closed_reduction {n k : ℕ} [NeZero n] (A : Automaton n) (hk : 1 ≤ k)
    (hA : A.IsAk k) (R : Finset (Fin n)) (hz : 0 ∈ R)
    (hcard : 2 ≤ R.card) (hproper : R.card < n)
    (hclosed : ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R) :
    ∃ c d : ℕ, 1 ≤ c ∧ 1 ≤ d ∧ c + d + 1 = n ∧
      d + 1 = R.card ∧
      ∃ B : Automaton (c + 1), ∃ C : Automaton (d + 1),
        B.IsAk k ∧ C.IsAk k ∧
        ∀ u v, B.IsReset u → C.IsReset v →
          ∃ w, A.IsReset w ∧ w.length = u.length + v.length := by sorry
