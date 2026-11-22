-- Prove2me | Theorems.Thm_Parikh_ParseTree_productionSize_plug
-- name    : Parikh.ParseTree.productionSize_plug
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:39.800794+00:00
-- url     : https://prove2.me/theorems/827f01e5-a810-49a2-9e4e-660a86dbebc4
-- title:
--   Parse Tree: production Size plug
-- statement:
--   Each hole contributes one copy of the inserted tree's production count.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreePlugging.lean#L70-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreePlugging.lean#L70-L87

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreePlugging
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree

theorem Parikh.ParseTree.productionSize_plug (E t : ParseTree T N) :
    (E.plug t).productionSize = E.productionSize + E.holes.length * t.productionSize := by sorry
