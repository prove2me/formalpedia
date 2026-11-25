-- Prove2me | Theorems.Thm_SinkReset_Plan_escape_to_Y
-- name    : SinkReset.Plan.escape_to_Y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:16.399799+00:00
-- url     : https://prove2.me/theorems/8c2b3a35-6318-4800-84b8-6f35a6599f96
-- title:
--   Plan: escape to Y
-- statement:
--   The Plan construction uses the escape to Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1120-L1126
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1120-L1126

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n k : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.escape_to_Y (hsc : SC A) (hne : (Y A).Nonempty) (x : Fin n)
    (hx : x ∈ Z A) :
    ∃ w, A.IsWord w ∧ w.length ≤ (Z A).card ∧ act w x ∈ Y A := by sorry
