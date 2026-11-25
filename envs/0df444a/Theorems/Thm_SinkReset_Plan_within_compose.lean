-- Prove2me | Theorems.Thm_SinkReset_Plan_within_compose
-- name    : SinkReset.Plan.within_compose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:25.597792+00:00
-- url     : https://prove2.me/theorems/d6f0e91b-2df4-4519-9d85-d77b78ea6347
-- title:
--   Plan: within compose
-- statement:
--   The Plan construction uses the within compose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L107-L113
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L107-L113

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.within_compose (S : Finset (Fin n)) (u : List (Letter n))
    (hu : A.IsWord u) (b : ℕ) (h : Within A (S.image (act u)) b) :
    Within A S (u.length + b) := by sorry
