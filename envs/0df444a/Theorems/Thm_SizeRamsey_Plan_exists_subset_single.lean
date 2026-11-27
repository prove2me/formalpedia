-- Prove2me | Theorems.Thm_SizeRamsey_Plan_exists_subset_single
-- name    : SizeRamsey.Plan.exists_subset_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:51.493166+00:00
-- url     : https://prove2.me/theorems/85543f0c-7dd5-566c-b149-ae6136968091
-- title:
--   Plan: exists subset single
-- statement:
--   The Plan construction uses the exists subset single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L127-L133
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L127-L133

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.exists_subset_single {V : Type*} (x₀ : V) (S : Finset V)
    (hS : S.card ≤ 1) : ∃ x, S ⊆ {x} := by sorry
