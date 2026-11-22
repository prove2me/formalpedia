-- Prove2me | Theorems.Thm_Parikh_ParseTree_height_le_height_plug
-- name    : Parikh.ParseTree.height_le_height_plug
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:47.112735+00:00
-- url     : https://prove2.me/theorems/0ac1a9a9-056a-462d-b4ba-db17019a3e90
-- title:
--   Parse Tree: height le height plug
-- statement:
--   Filling holes cannot reduce production height.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L39-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L39-L53

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree

theorem Parikh.ParseTree.height_le_height_plug (E t : ParseTree T N) : E.height ≤ (E.plug t).height := by sorry
