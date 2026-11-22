-- Prove2me | Theorems.Thm_Parikh_insertion_accounting
-- name    : Parikh.insertion_accounting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:12.807803+00:00
-- url     : https://prove2.me/theorems/d801fe50-44c8-4319-9f8d-d7eda6b0b31e
-- title:
--   Parikh: insertion accounting
-- statement:
--   Exact accounting, including zero-weight cycles (`lem:insertion-laws`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L103-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L103-L125

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

theorem Parikh.insertion_accounting [DecidableEq T] (g : ContextFreeGrammar T)
    (t C t' : ParseTree T g.NT) (h : Inserts g t C t') :
    t'.root = t.root ∧ t'.weight = t.weight + C.weight ∧
      t'.productionSize = t.productionSize + C.productionSize ∧
      t'.support = t.support ∪ C.support := by sorry
