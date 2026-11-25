-- Prove2me | Theorems.Thm_SinkReset_Plan_sum_values
-- name    : SinkReset.Plan.sum_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:17.032976+00:00
-- url     : https://prove2.me/theorems/9485600c-a49c-583d-a3be-9b4b5f528e98
-- title:
--   Plan: sum values
-- statement:
--   The Plan construction uses the sum values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1299-L1302
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1299-L1302

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.sum_values (n : ℕ) :
    potential Fin.val (Finset.univ : Finset (Fin n)) = n * (n - 1) / 2 := by sorry
