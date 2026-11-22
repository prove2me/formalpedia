-- Prove2me | Theorems.Thm_Parikh_ParseTree_plug_of_holes_eq_nil
-- name    : Parikh.ParseTree.plug_of_holes_eq_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:11.188953+00:00
-- url     : https://prove2.me/theorems/7a3859dc-7673-461f-ba3a-d8554ba8df38
-- title:
--   Parse Tree: plug of holes eq nil
-- statement:
--   A complete side branch is unchanged when another subtree fills holes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreeReplacement.lean#L35-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/TreeReplacement.lean#L35-L51

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree

theorem Parikh.ParseTree.plug_of_holes_eq_nil (E t : ParseTree T N) (hE : E.holes = []) :
    E.plug t = E := by sorry
