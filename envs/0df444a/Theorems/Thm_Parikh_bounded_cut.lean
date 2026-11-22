-- Prove2me | Theorems.Thm_Parikh_bounded_cut
-- name    : Parikh.bounded_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:21.8446+00:00
-- url     : https://prove2.me/theorems/42b72cbc-2653-477b-8e3e-715015166194
-- title:
--   Parikh: bounded cut
-- statement:
--   Remove a bounded cycle from a non-simple complete tree (`lem:cut`).
--   The smaller tree remains complete and has the same root. Inserting the returned
--   context reconstructs the original tree, and production size strictly decreases.
--   Choosing a minimal non-simple subtree bounds the context's side branches as
--   well as the path between repeated labels.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L145-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L145-L213

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.bounded_cut (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) (hs : ¬ t.Simple) :
    ∃ smaller C, Complete g smaller ∧ smaller.root = t.root ∧
      IsBoundedCycle g C ∧ Inserts g smaller C t ∧
      smaller.productionSize < t.productionSize := by sorry
