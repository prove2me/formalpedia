-- Prove2me | Theorems.Thm_SinkReset_Plan_potential_bound
-- name    : SinkReset.Plan.potential_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:42:51.944751+00:00
-- url     : https://prove2.me/theorems/e7e394a6-6d2e-430d-bad3-62bfbcba5427
-- title:
--   Plan: potential bound
-- statement:
--   The Plan construction uses the potential bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1257-L1263
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1257-L1263

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.potential_bound {n : ℕ} [NeZero n] (A : Automaton n)
    (weight : Fin n → ℕ) (hzero : weight 0 = 0)
    (hstep : ∀ a ∈ A.letters, ∀ S : Finset (Fin n),
      potential weight S ≤ potential weight (S.image a) + 1)
    (w : List (Letter n)) (hw : A.IsReset w) :
    potential weight Finset.univ ≤ w.length := by sorry
