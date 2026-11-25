-- Prove2me | Theorems.Thm_SinkReset_Plan_distance_Y
-- name    : SinkReset.Plan.distance_Y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:31.0736+00:00
-- url     : https://prove2.me/theorems/86982f40-e180-58aa-aafe-0bf608e3845a
-- title:
--   Plan: distance Y
-- statement:
--   The Plan construction uses the distance Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L465-L470
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L465-L470

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.distance_Y {d : Fin n → ℕ} (hd : Distances A d) :
    (∀ q, d q ≤ (Y A).card + 1) ∧
    ((Y A).Nonempty → ∃ y ∈ Y A, d y = 2) := by sorry
