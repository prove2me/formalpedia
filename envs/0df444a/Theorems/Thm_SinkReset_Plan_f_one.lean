-- Prove2me | Theorems.Thm_SinkReset_Plan_f_one
-- name    : SinkReset.Plan.f_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:42.789812+00:00
-- url     : https://prove2.me/theorems/97466ae6-47e0-45d2-aca7-87885acf26f2
-- title:
--   Plan: f one
-- statement:
--   The Plan construction uses the f one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L734-L738
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L734-L738

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.f_one (n : ℕ) : f 1 n = n * (n - 1) / 2 := by sorry
