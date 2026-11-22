-- Prove2me | Theorems.Thm_Parikh_Valid_frontier_step
-- name    : Parikh.Valid.frontier_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:13.277389+00:00
-- url     : https://prove2.me/theorems/9dfeb094-b6ea-42e0-9e24-232dc08fe103
-- title:
--   Valid: frontier step
-- statement:
--   A rewrite expands one frontier hole, preserving validity and the tree root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L390-L462
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L390-L462

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
variable {N : Type*}

theorem Parikh.Valid.frontier_step {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) {v : List (Symbol T g.NT)} (h : g.Produces t.frontier v) :
    ∃ t', Valid g t' ∧ t'.root = t.root ∧ t'.frontier = v := by sorry
