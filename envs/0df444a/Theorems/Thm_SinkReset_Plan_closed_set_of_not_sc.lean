-- Prove2me | Theorems.Thm_SinkReset_Plan_closed_set_of_not_sc
-- name    : SinkReset.Plan.closed_set_of_not_sc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:06.945497+00:00
-- url     : https://prove2.me/theorems/b715f3a2-e4fb-4c5f-aa11-be8f90807ab5
-- title:
--   Plan: closed set of not sc
-- statement:
--   The Plan construction uses the closed set of not sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L616-L619
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L616-L619

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.closed_set_of_not_sc {n : ℕ} [NeZero n] (A : Automaton n) (h : ¬ SC A) :
    ∃ R : Finset (Fin n), 0 ∈ R ∧ 2 ≤ R.card ∧ R.card < n ∧
      ∀ a ∈ A.letters, ∀ q ∈ R, a q ∈ R := by sorry
