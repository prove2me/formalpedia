-- Prove2me | Theorems.Thm_SinkReset_Plan_wins_push
-- name    : SinkReset.Plan.wins_push
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:19.712126+00:00
-- url     : https://prove2.me/theorems/9f74ab05-8f84-4ec3-8a23-bbd31205e868
-- title:
--   Plan: wins push
-- statement:
--   The Plan construction uses the wins push property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L527-L550
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L527-L550

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)

theorem SinkReset.Plan.wins_push
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (φ : Fin n → Fin m) (hzero : φ 0 = 0)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (a q) = τ a (φ q))
    {k : ℕ} {S : Finset (Fin n)} (h : A.AliceWins k S) :
    B.AliceWins k (S.image φ) := by sorry
