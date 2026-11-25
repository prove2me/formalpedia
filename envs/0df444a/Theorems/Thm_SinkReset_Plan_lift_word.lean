-- Prove2me | Theorems.Thm_SinkReset_Plan_lift_word
-- name    : SinkReset.Plan.lift_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:44.251352+00:00
-- url     : https://prove2.me/theorems/8ccc2f15-13c4-4cb0-ad7b-ee200dd9d21e
-- title:
--   Plan: lift word
-- statement:
--   The Plan construction uses the lift word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L490-L503
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L490-L503

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)

theorem SinkReset.Plan.lift_word
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (v : List (Letter m)) (hv : B.IsWord v) :
    ∃ u, A.IsWord u ∧ u.map τ = v ∧ u.length = v.length := by sorry
