-- Prove2me | Theorems.Thm_Parikh_insertion_enabled
-- name    : Parikh.insertion_enabled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:07.618458+00:00
-- url     : https://prove2.me/theorems/f2503bcd-0399-44d8-bbb0-532a364d8d29
-- title:
--   Parikh: insertion enabled
-- statement:
--   Support means an internal occurrence, including an empty-production node (`lem:enabled`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L84-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L84-L100

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

theorem Parikh.insertion_enabled (g : ContextFreeGrammar T) (t C : ParseTree T g.NT)
    (A : g.NT) (ht : Complete g t) (hC : Cycle g C A) :
    (∃ t', Inserts g t C t') ↔ A ∈ t.support := by sorry
