-- Prove2me | Theorems.Thm_RamanujanNested_rollUp_succ
-- name    : RamanujanNested.rollUp_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-27T04:59:03.382855+00:00
-- url     : https://prove2.me/theorems/bc36b98a-bfa8-4b28-b242-6925dbc7b8a6
-- title:
--   Ramanujan Nested: roll Up succ
-- statement:
--   Unfolding lemma for `rollUp`, stated explicitly so later proofs don't rely on
--   definitional unfolding firing silently.
--
--   Source: https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Defs.lean#L41-L42
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Defs.lean#L41-L42

module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_RamanujanNested_Defs
set_option autoImplicit true
@[expose] public section
open RamanujanNested

theorem RamanujanNested.rollUp_succ (a : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    rollUp a T (n + 1) = Real.sqrt (1 + a 1 * rollUp (fun k => a (k + 1)) T n) := by sorry
