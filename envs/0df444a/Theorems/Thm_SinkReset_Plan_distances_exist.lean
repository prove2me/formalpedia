-- Prove2me | Theorems.Thm_SinkReset_Plan_distances_exist
-- name    : SinkReset.Plan.distances_exist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:26.056179+00:00
-- url     : https://prove2.me/theorems/2daae84f-ffac-409f-9065-2c9c019cea37
-- title:
--   Plan: distances exist
-- statement:
--   The Plan construction uses the distances exist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L438-L441
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L438-L441

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.distances_exist (h : ∃ w, A.IsReset w) :
    ∃ d, Distances A d := by sorry
