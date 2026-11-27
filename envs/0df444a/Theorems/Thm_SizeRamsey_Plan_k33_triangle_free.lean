-- Prove2me | Theorems.Thm_SizeRamsey_Plan_k33_triangle_free
-- name    : SizeRamsey.Plan.k33_triangle_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:40.862599+00:00
-- url     : https://prove2.me/theorems/d191eae1-08d7-5f80-a01e-638ae7d38f56
-- title:
--   Plan: k33 triangle free
-- statement:
--   The Plan construction uses the k33 triangle free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L63-L66
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L63-L66

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.k33_triangle_free :
    ∀ a b c, k33MinusEdge.Adj a b →
      k33MinusEdge.Adj b c → ¬ k33MinusEdge.Adj c a := by sorry
