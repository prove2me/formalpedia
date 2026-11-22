-- Prove2me | Theorems.Thm_Parikh_EncodedGrammar_mem_cycleTrees
-- name    : Parikh.EncodedGrammar.mem_cycleTrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:52:34.355051+00:00
-- url     : https://prove2.me/theorems/58912bfd-c928-4b5d-aea0-5e04876d9f38
-- title:
--   Encoded Grammar: mem cycle Trees
-- statement:
--   Cycle enumeration uses precisely the frozen active-height predicate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L136-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L136-L152

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar

theorem Parikh.EncodedGrammar.mem_cycleTrees (g : EncodedGrammar)
    (C : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :
    C ∈ g.cycleTrees ↔ IsBoundedCycle g.decode C := by sorry
