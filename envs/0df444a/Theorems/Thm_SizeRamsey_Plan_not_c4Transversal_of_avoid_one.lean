-- Prove2me | Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_avoid_one
-- name    : SizeRamsey.Plan.not_c4Transversal_of_avoid_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:16.884912+00:00
-- url     : https://prove2.me/theorems/ebee0b68-1bf7-53ec-a9eb-4ca78b02026a
-- title:
--   Plan: not c4 Transversal of avoid one
-- statement:
--   Lower bound `τ₄ ≥ 2` from a table: every vertex is avoided by some square.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L136-L144
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L136-L144

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.not_c4Transversal_of_avoid_one {V : Type*} {G : SimpleGraph V}
    (x₀ : V)
    (h : ∀ x : V, ∃ a b c d : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧
      a ≠ c ∧ b ≠ d ∧ a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x)
    (S : Finset V) (hS : S.card < 2) : ¬ c4Transversal G S := by sorry
