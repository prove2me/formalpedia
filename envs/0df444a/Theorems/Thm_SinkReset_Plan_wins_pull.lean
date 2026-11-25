-- Prove2me | Theorems.Thm_SinkReset_Plan_wins_pull
-- name    : SinkReset.Plan.wins_pull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:06.695881+00:00
-- url     : https://prove2.me/theorems/ded46476-ca97-42bf-8971-23050e26ad80
-- title:
--   Plan: wins pull
-- statement:
--   The Plan construction uses the wins pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L551-L578
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L551-L578

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

theorem SinkReset.Plan.wins_pull
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (φ : Fin m → Fin n) (hzero : ∀ q, φ q = 0 ↔ q = 0)
    (hcomm : ∀ a ∈ A.letters, ∀ q, φ (τ a q) = a (φ q))
    {k : ℕ} (S : Finset (Fin m)) (h : A.AliceWins k (S.image φ)) :
    B.AliceWins k S := by sorry
