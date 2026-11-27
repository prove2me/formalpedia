-- Prove2me | Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_avoid_pair
-- name    : SizeRamsey.Plan.not_c4Transversal_of_avoid_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:51.364373+00:00
-- url     : https://prove2.me/theorems/7567941c-f013-445a-af4b-4f3649ca69c0
-- title:
--   Plan: not c4 Transversal of avoid pair
-- statement:
--   Lower bound `τ₄ ≥ 3` from a table: every pair of vertices is avoided by some square.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L116-L125
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L116-L125

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.not_c4Transversal_of_avoid_pair {V : Type*} {G : SimpleGraph V}
    (x₀ : V)
    (h : ∀ x y : V, ∃ a b c d : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧
      a ≠ c ∧ b ≠ d ∧ a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x ∧ a ≠ y ∧ b ≠ y ∧ c ≠ y ∧ d ≠ y)
    (S : Finset V) (hS : S.card < 3) : ¬ c4Transversal G S := by sorry
