-- Prove2me | Theorems.Thm_Parikh_ParseTree_mem_nodeFamily
-- name    : Parikh.ParseTree.mem_nodeFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:17.582795+00:00
-- url     : https://prove2.me/theorems/3e1a1773-8d78-4c09-8dc3-79426fd7175e
-- title:
--   Parse Tree: mem node Family
-- statement:
--   The Parse Tree construction uses the mem node Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L69-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L69-L78

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

theorem Parikh.ParseTree.mem_nodeFamily (r : ContextFreeRule T N) (family : Finset (ParseTree T N))
    (children : List (ParseTree T N)) (hlen : children.length = r.output.length)
    (hchildren : ∀ c ∈ children, c ∈ family) : node r children ∈ nodeFamily r family := by sorry
