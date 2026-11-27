-- Prove2me | Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_card_lt_one
-- name    : SizeRamsey.Plan.not_c4Transversal_of_card_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:55.47136+00:00
-- url     : https://prove2.me/theorems/ec086953-6af8-5a3f-aa9c-4f6a5e0f7fb7
-- title:
--   Plan: not c4 Transversal of card lt one
-- statement:
--   Lower bound `τ₄ ≥ 1` from one square.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L147-L152
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L147-L152

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.not_c4Transversal_of_card_lt_one {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) (S : Finset V) (hS : S.card < 1) : ¬ c4Transversal G S := by sorry
