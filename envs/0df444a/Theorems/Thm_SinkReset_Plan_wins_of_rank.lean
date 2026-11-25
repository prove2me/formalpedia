-- Prove2me | Theorems.Thm_SinkReset_Plan_wins_of_rank
-- name    : SinkReset.Plan.wins_of_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:43.49027+00:00
-- url     : https://prove2.me/theorems/443c7c46-6152-4bb7-af89-12e6da00cdd6
-- title:
--   Plan: wins of rank
-- statement:
--   The Plan construction uses the wins of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L235-L240
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L235-L240

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.wins_of_rank {k : ℕ} (rank : Finset (Fin n) → ℕ)
    (hstep : ∀ S, (active S).Nonempty → ∃ a ∈ A.letters,
      ∀ u, A.IsWord u → u.length < k →
        rank (S.image (act (a :: u))) < rank S) :
    ∀ S, A.AliceWins k S := by sorry
