-- Prove2me | Theorems.Thm_SinkReset_Plan_distance_facts
-- name    : SinkReset.Plan.distance_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:43.046182+00:00
-- url     : https://prove2.me/theorems/793c97ba-f201-4100-a856-d87190cbb51b
-- title:
--   Plan: distance facts
-- statement:
--   The Plan construction uses the distance facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L448-L464
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L448-L464

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.distance_facts {d : Fin n → ℕ} (hd : Distances A d) :
    d 0 = 0 ∧
    (∀ q, (d q = 1 ↔ q ∈ Z A) ∧ (q ∈ Y A ↔ 2 ≤ d q)) ∧
    (∀ q a, a ∈ A.letters → d q ≤ d (a q) + 1) := by sorry
