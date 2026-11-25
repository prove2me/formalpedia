-- Prove2me | Theorems.Thm_SinkReset_Plan_no_return
-- name    : SinkReset.Plan.no_return
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:18.821054+00:00
-- url     : https://prove2.me/theorems/7025c4b0-ff43-4a73-90a0-7ec0fe9581fb
-- title:
--   Plan: no return
-- statement:
--   The Plan construction uses the no return property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1132-L1165
-- source:
--   https://github.com/benkeene/sink-reset-thresholds/blob/0a4048a517c5a1e6382e0726f39ea125eddb658a/SinkReset/Plan.lean#L1132-L1165

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n k : ℕ} [NeZero n] (A : Automaton n)

theorem SinkReset.Plan.no_return (hk : 2 ≤ k) (hA : A.IsAk k) {d : Fin n → ℕ}
    (hd : Distances A d) (y₁ y₂ : Fin n) (hY : Y A = {y₁, y₂})
    (h₁ : d y₁ = 2) (h₂ : d y₂ = 3) :
    (∀ a ∈ A.letters, a y₂ = y₁ ∨ a y₂ = y₂) ∧
    (∃ c ∈ A.letters, c y₂ = y₁) ∧
    (∀ a ∈ A.letters, a y₁ ≠ y₂) := by sorry
