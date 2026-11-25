-- Prove2me | Theorems.Thm_SinkReset_exists_isAk_reset_ge_dev
-- name    : SinkReset.exists_isAk_reset_ge_dev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:31.879373+00:00
-- url     : https://prove2.me/theorems/8843c09e-5ff9-4faf-95a3-115dd4cdb041
-- title:
--   Sink Reset: exists is Ak reset ge dev
-- statement:
--   The Sink Reset construction uses the exists is Ak reset ge dev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2135-L2137
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L2135-L2137

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset

theorem SinkReset.exists_isAk_reset_ge_dev (n k : ℕ) [NeZero n] (hn : 2 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 ∨ n ≤ k + 3) : ∃ A : Automaton n, A.IsAk k ∧ ∀ w, A.IsReset w → f k n ≤ w.length := by sorry
