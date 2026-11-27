-- Prove2me | Theorems.Thm_SizeRamsey_Plan_k33_avoid_one
-- name    : SizeRamsey.Plan.k33_avoid_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:24.429971+00:00
-- url     : https://prove2.me/theorems/c7ce7516-b62d-417e-883c-e6f60efc2cfc
-- title:
--   Plan: k33 avoid one
-- statement:
--   The Plan construction uses the k33 avoid one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L68-L71
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L68-L71

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.k33_avoid_one : ∀ x : Fin 6, ∃ a b c d : Fin 6, k33MinusEdge.Adj a b ∧
    k33MinusEdge.Adj b c ∧ k33MinusEdge.Adj c d ∧ k33MinusEdge.Adj d a ∧ a ≠ c ∧ b ≠ d ∧
    a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x := by sorry
