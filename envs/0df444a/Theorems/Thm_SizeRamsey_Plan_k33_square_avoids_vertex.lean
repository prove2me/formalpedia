-- Prove2me | Theorems.Thm_SizeRamsey_Plan_k33_square_avoids_vertex
-- name    : SizeRamsey.Plan.k33_square_avoids_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:40.516639+00:00
-- url     : https://prove2.me/theorems/67c2e585-60d5-583f-807a-f28c3ff93ddc
-- title:
--   Plan: k33 square avoids vertex
-- statement:
--   The Plan construction uses the k33 square avoids vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L52-L61
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L52-L61

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.k33_square_avoids_vertex (v : Fin 6) :
    ∃ f : Fin 4 → Fin 6,
      IsC4Map k33MinusEdge f ∧ ∀ i, f i ≠ v := by sorry
