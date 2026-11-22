-- Prove2me | Theorems.Thm_Parikh_ParseTree_height_child_lt
-- name    : Parikh.ParseTree.height_child_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:35.811803+00:00
-- url     : https://prove2.me/theorems/ca53cdab-a723-4a18-bd98-34e9155d521a
-- title:
--   Parse Tree: height child lt
-- statement:
--   Every child's height is strictly smaller than its production node's height.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L55-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L55-L60

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.ParseTree
variable {T N : Type*}

theorem Parikh.ParseTree.height_child_lt (r : ContextFreeRule T N) (children : List (ParseTree T N))
    (c : ParseTree T N) (hc : c ∈ children) : c.height < (node r children).height := by sorry
