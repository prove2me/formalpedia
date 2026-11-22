-- Prove2me | Theorems.Thm_Parikh_ParseTree_frontier_of_holes_eq_nil
-- name    : Parikh.ParseTree.frontier_of_holes_eq_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:22.112879+00:00
-- url     : https://prove2.me/theorems/4aefc445-10fb-4901-957d-6782dd9db743
-- title:
--   Parse Tree: frontier of holes eq nil
-- statement:
--   A tree with no holes has a wholly terminal frontier.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L343-L362
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean#L343-L362

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

theorem Parikh.ParseTree.frontier_of_holes_eq_nil (t : ParseTree T N) (h : t.holes = []) :
    t.frontier = t.yield.map Symbol.terminal := by sorry
