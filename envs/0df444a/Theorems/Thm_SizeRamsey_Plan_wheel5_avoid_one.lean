-- Prove2me | Theorems.Thm_SizeRamsey_Plan_wheel5_avoid_one
-- name    : SizeRamsey.Plan.wheel5_avoid_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:18.232075+00:00
-- url     : https://prove2.me/theorems/6efc9e3b-8414-4b16-8400-c688af3cdc15
-- title:
--   Plan: wheel5 avoid one
-- statement:
--   The Plan construction uses the wheel5 avoid one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L64-L66
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L64-L66

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.wheel5_avoid_one : ∀ x : Fin 5, ∃ a b c d : Fin 5, wheel5.Adj a b ∧ wheel5.Adj b c ∧
    wheel5.Adj c d ∧ wheel5.Adj d a ∧ a ≠ c ∧ b ≠ d ∧ a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x := by sorry
