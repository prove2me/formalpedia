-- Prove2me | Theorems.Thm_Parikh_ParseTree_count_yield_plug
-- name    : Parikh.ParseTree.count_yield_plug
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:00.719299+00:00
-- url     : https://prove2.me/theorems/856f786e-7c45-48df-b8d5-d08a3eddfbf3
-- title:
--   Parse Tree: count yield plug
-- statement:
--   Terminal counts add once for each hole, regardless of its frontier position.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreePlugging.lean#L90-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreePlugging.lean#L90-L107

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreePlugging
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree

theorem Parikh.ParseTree.count_yield_plug [DecidableEq T] (E t : ParseTree T N) (a : T) :
    (E.plug t).yield.count a = E.yield.count a + E.holes.length * t.yield.count a := by sorry
