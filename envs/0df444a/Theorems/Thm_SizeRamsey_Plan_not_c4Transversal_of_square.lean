-- Prove2me | Theorems.Thm_SizeRamsey_Plan_not_c4Transversal_of_square
-- name    : SizeRamsey.Plan.not_c4Transversal_of_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:19.992467+00:00
-- url     : https://prove2.me/theorems/eb18244b-b002-544e-aaf4-b3f39fcc291b
-- title:
--   Plan: not c4 Transversal of square
-- statement:
--   A square avoiding `S` shows that `S` is not a transversal.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L95-L102
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L95-L102

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.not_c4Transversal_of_square {V : Type*} {G : SimpleGraph V} {S : Finset V}
    {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d)
    (havoid : a ∉ S ∧ b ∉ S ∧ c ∉ S ∧ d ∉ S) : ¬ c4Transversal G S := by sorry
