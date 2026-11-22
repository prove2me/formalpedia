-- Prove2me | Theorems.Thm_Parikh_InsertionSequence_append
-- name    : Parikh.InsertionSequence.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:19.951893+00:00
-- url     : https://prove2.me/theorems/15f667e6-1a3f-4eb8-a041-a65866366549
-- title:
--   Insertion Sequence: append
-- statement:
--   Concatenate insertion sequences, retaining the ordered list of contexts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L216-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L216-L223

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

theorem Parikh.InsertionSequence.append {g : ContextFreeGrammar T}
    {B middle t : ParseTree T g.NT} {Cs Ds : List (ParseTree T g.NT)}
    (first : InsertionSequence g B Cs middle)
    (second : InsertionSequence g middle Ds t) :
    InsertionSequence g B (Cs ++ Ds) t := by sorry
