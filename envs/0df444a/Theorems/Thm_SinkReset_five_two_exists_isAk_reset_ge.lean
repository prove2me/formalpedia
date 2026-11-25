-- Prove2me | Theorems.Thm_SinkReset_five_two_exists_isAk_reset_ge
-- name    : SinkReset.five_two_exists_isAk_reset_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:20.321477+00:00
-- url     : https://prove2.me/theorems/e34a77b6-eb2b-5f0b-bbad-1c51fa6c96be
-- title:
--   Sink Reset: five two exists is Ak reset ge
-- statement:
--   M(5,2) ≥ 6: some 5-state A_2 automaton with sink 0 has no reset word of length less than 6 (CLAIM.md headline; PROOF.md §4 Lemma 14, the automaton C_{2,2}).
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/Solution.lean#L37-L38
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/Solution.lean#L37-L38

module
public import Mathlib
public import Definitions.Def_SinkReset
public import Definitions.Def_SinkResetThresholds_Solution
set_option autoImplicit false
@[expose] public section
public section
open SinkReset

theorem SinkReset.five_two_exists_isAk_reset_ge : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length := by sorry
