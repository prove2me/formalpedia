-- Prove2me | Theorems.Thm_Parikh_ParseTree_frontier_holes
-- name    : Parikh.ParseTree.frontier_holes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:16.171011+00:00
-- url     : https://prove2.me/theorems/4d7d4af5-f739-4b3f-b6fe-1ff89103d71e
-- title:
--   Parse Tree: frontier holes
-- statement:
--   The nonterminals on the frontier are exactly the holes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L305-L321
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L305-L321

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

theorem Parikh.ParseTree.frontier_holes (t : ParseTree T N) :
    (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal _ => none | .nonterminal A => some A) = t.holes := by sorry
