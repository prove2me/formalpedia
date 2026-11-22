-- Prove2me | Theorems.Thm_Parikh_derives_tree_frontier
-- name    : Parikh.derives_tree_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:15.857192+00:00
-- url     : https://prove2.me/theorems/9b5ed001-eca7-48e6-88c0-8c60d1072acb
-- title:
--   Parikh: derives tree frontier
-- statement:
--   Any derivation from a nonterminal is the frontier of a valid open tree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L465-L473
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L465-L473

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

theorem Parikh.derives_tree_frontier (g : ContextFreeGrammar T) (A : g.NT)
    {v : List (Symbol T g.NT)} (h : g.Derives [.nonterminal A] v) :
    ∃ t, Valid g t ∧ t.root = .nonterminal A ∧ t.frontier = v := by sorry
