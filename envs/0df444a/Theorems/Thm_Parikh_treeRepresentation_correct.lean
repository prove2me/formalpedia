-- Prove2me | Theorems.Thm_Parikh_treeRepresentation_correct
-- name    : Parikh.treeRepresentation_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:30.628407+00:00
-- url     : https://prove2.me/theorems/64b04543-5737-4cd3-b740-b400f4611e1d
-- title:
--   Parikh: tree Representation correct
-- statement:
--   The exact tree formula and its semilinearity together give the grammar image
--   (`thm:main`, `thm:parikh-statement`). No finite nonterminal assumption is needed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarImage.lean#L39-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarImage.lean#L39-L67

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_FiniteRepresentation
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Definitions.Def_LeanPool_Parikh_GrammarImage
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.treeRepresentation_correct [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language ∧ IsSemilinearSet (image g.language) := by sorry
