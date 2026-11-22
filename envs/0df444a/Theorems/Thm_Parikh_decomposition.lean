-- Prove2me | Theorems.Thm_Parikh_decomposition
-- name    : Parikh.decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:14.844866+00:00
-- url     : https://prove2.me/theorems/03e2216d-adb7-43f7-b940-c466baca44e3
-- title:
--   Parikh: decomposition
-- statement:
--   Every complete tree can be rebuilt from a simple complete tree by inserting
--   bounded cycle contexts (`thm:decomposition`).
--   The insertion list retains actual contexts and their order, so reconstruction
--   recovers the tree itself. The proof repeatedly applies `bounded_cut`, using
--   production count for strong induction; zero-weight cycles still decrease this
--   measure when removed. The simple tree has the same root as the original.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L231-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L231-L249

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

theorem Parikh.decomposition (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) :
    ∃ B Cs, Complete g B ∧ B.root = t.root ∧ B.Simple ∧
      (∀ C ∈ Cs, IsBoundedCycle g C) ∧ InsertionSequence g B Cs t := by sorry
