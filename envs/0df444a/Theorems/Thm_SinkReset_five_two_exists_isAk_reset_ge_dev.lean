-- Prove2me | Theorems.Thm_SinkReset_five_two_exists_isAk_reset_ge_dev
-- name    : SinkReset.five_two_exists_isAk_reset_ge_dev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:08.580046+00:00
-- url     : https://prove2.me/theorems/c579f163-a043-48b1-8017-cdd4f072cc85
-- title:
--   Sink Reset: five two exists is Ak reset ge dev
-- statement:
--   The Sink Reset construction uses the five two exists is Ak reset ge dev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2144-L2147
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2144-L2147

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset

theorem SinkReset.five_two_exists_isAk_reset_ge_dev : ∃ A : Automaton 5, A.IsAk 2 ∧ ∀ w, A.IsReset w → 6 ≤ w.length := by sorry
