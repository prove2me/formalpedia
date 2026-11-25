-- Prove2me | Theorems.Thm_SinkReset_Plan_bob_first_iff
-- name    : SinkReset.Plan.bob_first_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:02.857733+00:00
-- url     : https://prove2.me/theorems/6cc453d1-9886-44eb-8ffc-49dd836f1a78
-- title:
--   Plan: bob first iff
-- statement:
--   The Plan construction uses the bob first iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L182-L193
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L182-L193

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.bob_first_iff {k : ℕ} (hk : 1 ≤ k) :
    A.IsAk k ↔ ∀ u, A.IsWord u → u.length < k →
      A.AliceWins k (Finset.univ.image (act u)) := by sorry
