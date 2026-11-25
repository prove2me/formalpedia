-- Prove2me | Theorems.Thm_SinkReset_Plan_trap
-- name    : SinkReset.Plan.trap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:42.029801+00:00
-- url     : https://prove2.me/theorems/eb52c068-cc77-4584-ad08-c7acce52ba12
-- title:
--   Plan: trap
-- statement:
--   The Plan construction uses the trap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L210-L216
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L210-L216

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.trap {k : ℕ} (T : Finset (Fin n)) (hne : T.Nonempty) (hzero : 0 ∉ T)
    (hreply : ∀ t ∈ T, ∀ a ∈ A.letters, ∃ u,
      A.IsWord u ∧ u.length < k ∧ act (a :: u) t ∈ T) :
    ¬ A.IsAk k := by sorry
