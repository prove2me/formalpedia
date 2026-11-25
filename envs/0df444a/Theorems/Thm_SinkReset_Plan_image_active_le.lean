-- Prove2me | Theorems.Thm_SinkReset_Plan_image_active_le
-- name    : SinkReset.Plan.image_active_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:23.839452+00:00
-- url     : https://prove2.me/theorems/35e5f637-f7f9-5dfe-897f-e0b73f8feda5
-- title:
--   Plan: image active le
-- statement:
--   The Plan construction uses the image active le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L99-L102
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L99-L102

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.image_active_le (S : Finset (Fin n)) (w : List (Letter n))
    (hw : A.IsWord w) :
    (active (S.image (act w))).card ≤ (active S).card := by sorry
