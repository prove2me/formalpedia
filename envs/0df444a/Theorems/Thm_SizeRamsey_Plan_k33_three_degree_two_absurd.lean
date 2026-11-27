-- Prove2me | Theorems.Thm_SizeRamsey_Plan_k33_three_degree_two_absurd
-- name    : SizeRamsey.Plan.k33_three_degree_two_absurd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:35.123798+00:00
-- url     : https://prove2.me/theorems/cfe83bee-7da3-5dbf-ac15-f3a8de8ce847
-- title:
--   Plan: k33 three degree two absurd
-- statement:
--   The Plan construction uses the k33 three degree two absurd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L116-L118
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L116-L118

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.k33_three_degree_two_absurd : ∀ x y z : Fin 6, x ≠ y → x ≠ z → y ≠ z →
    (x = 0 ∨ x = 3) → (y = 0 ∨ y = 3) → (z = 0 ∨ z = 3) → False := by sorry
