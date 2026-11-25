-- Prove2me | Theorems.Thm_SinkReset_Plan_cycle_rank_step
-- name    : SinkReset.Plan.cycle_rank_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:36.490864+00:00
-- url     : https://prove2.me/theorems/d38f48e3-5291-428b-bc79-b1323f3359c5
-- title:
--   Plan: cycle rank step
-- statement:
--   The Plan construction uses the cycle rank step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1715-L1768
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1715-L1768

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan

theorem SinkReset.Plan.cycle_rank_step {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (S : Finset (Fin (k + m + 1))) (hne : (active S).Nonempty) :
    ∃ a ∈ (cycle k m).letters, ∀ u, (cycle k m).IsWord u → u.length < k →
      cycleRank k m (S.image (act (a :: u))) < cycleRank k m S := by sorry
