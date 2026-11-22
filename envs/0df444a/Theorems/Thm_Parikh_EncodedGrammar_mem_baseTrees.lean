-- Prove2me | Theorems.Thm_Parikh_EncodedGrammar_mem_baseTrees
-- name    : Parikh.EncodedGrammar.mem_baseTrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:52:34.885807+00:00
-- url     : https://prove2.me/theorems/1dd308db-0108-4c14-930d-858ee91e0a29
-- title:
--   Encoded Grammar: mem base Trees
-- statement:
--   Every simple complete start tree is enumerated, including epsilon trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L118-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean#L118-L133

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
public import Definitions.Def_LeanPool_Parikh_CompilerTrees
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.EncodedGrammar

theorem Parikh.EncodedGrammar.mem_baseTrees (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :
    B ∈ g.baseTrees ↔ IsBase g.decode B := by sorry
