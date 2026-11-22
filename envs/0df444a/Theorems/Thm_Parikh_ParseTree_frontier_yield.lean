-- Prove2me | Theorems.Thm_Parikh_ParseTree_frontier_yield
-- name    : Parikh.ParseTree.frontier_yield
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:12.95164+00:00
-- url     : https://prove2.me/theorems/6f4ac2d6-9951-48ff-8fe4-f77227244148
-- title:
--   Parse Tree: frontier yield
-- statement:
--   The terminals on the frontier are exactly the yield.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L324-L340
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L324-L340

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
open Parikh.ParseTree

theorem Parikh.ParseTree.frontier_yield (t : ParseTree T N) :
    (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal a => some a | .nonterminal _ => none) = t.yield := by sorry
