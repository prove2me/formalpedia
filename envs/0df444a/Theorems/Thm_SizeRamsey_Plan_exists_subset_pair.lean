-- Prove2me | Theorems.Thm_SizeRamsey_Plan_exists_subset_pair
-- name    : SizeRamsey.Plan.exists_subset_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:52.319189+00:00
-- url     : https://prove2.me/theorems/095fc5c8-f6d2-4aa7-b4c5-d0768ac5e6c6
-- title:
--   Plan: exists subset pair
-- statement:
--   The Plan construction uses the exists subset pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L104-L113
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L104-L113

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.exists_subset_pair {V : Type*} [DecidableEq V] (x₀ : V) (S : Finset V)
    (hS : S.card ≤ 2) : ∃ x y, S ⊆ {x, y} := by sorry
