-- Prove2me | Theorems.Thm_Parikh_ParseTree_exists_root_mem_child_support
-- name    : Parikh.ParseTree.exists_root_mem_child_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:56.490128+00:00
-- url     : https://prove2.me/theorems/c1bbbb30-d5ea-4402-a342-f5b6d7c9a439
-- title:
--   Parse Tree: exists root mem child support
-- statement:
--   With simple children, a non-simple node repeats its root in a child.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L105-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L105-L118

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

theorem Parikh.ParseTree.exists_root_mem_child_support (r : ContextFreeRule T N)
    (cs : List (ParseTree T N)) (hs : ¬ (node r cs).Simple)
    (hc : ∀ c ∈ cs, c.Simple) : ∃ c ∈ cs, r.input ∈ c.support := by sorry
